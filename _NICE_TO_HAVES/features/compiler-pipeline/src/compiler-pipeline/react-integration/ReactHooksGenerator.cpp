// React Hooks Generator - Phase 4
#include "ReactHooksGenerator.h"
#include "Cpp23Parser.h"
#include <string>
#include <sstream>
#include <vector>
#include <map>

namespace react_hooks_generator {

// Generate React hooks from C++23 component
std::string generate_react_hooks(const CppStruct& component_def) {
    std::ostringstream oss;
    
    // Analyze component for hook needs
    bool has_state = has_state_fields(component_def);
    bool has_effects = has_effect_fields(component_def);
    bool has_refs = has_ref_fields(component_def);
    bool has_callbacks = has_callback_fields(component_def);
    
    oss << "// React Hooks for " << component_def.name << "\n";
    oss << "import { useState, useEffect, useRef, useCallback, useMemo } from 'react';\n\n";
    
    // Generate useState hooks
    if (has_state) {
        oss << generate_use_state_hooks(component_def);
    }
    
    // Generate useEffect hooks
    if (has_effects) {
        oss << generate_use_effect_hooks(component_def);
    }
    
    // Generate useRef hooks
    if (has_refs) {
        oss << generate_use_ref_hooks(component_def);
    }
    
    // Generate useCallback hooks
    if (has_callbacks) {
        oss << generate_use_callback_hooks(component_def);
    }
    
    // Generate useMemo hooks
    oss << generate_use_memo_hooks(component_def);
    
    return oss.str();
}

// Check if component has state fields
bool has_state_fields(const CppStruct& component_def) {
    for (const auto& field : component_def.fields) {
        if (field.attributes.find("state") != field.attributes.end()) {
            return true;
        }
    }
    return false;
}

// Check if component has effect fields
bool has_effect_fields(const CppStruct& component_def) {
    for (const auto& func : component_def.functions) {
        if (func.attributes.find("effect") != func.attributes.end()) {
            return true;
        }
    }
    return false;
}

// Check if component has ref fields
bool has_ref_fields(const CppStruct& component_def) {
    for (const auto& field : component_def.fields) {
        if (field.type.name.find("Ref") != std::string::npos ||
            field.attributes.find("ref") != field.attributes.end()) {
            return true;
        }
    }
    return false;
}

// Check if component has callback fields
bool has_callback_fields(const CppStruct& component_def) {
    for (const auto& field : component_def.fields) {
        if (field.type.name.find("function") != std::string::npos ||
            field.type.name.find("callback") != std::string::npos) {
            return true;
        }
    }
    return false;
}

// Generate useState hooks
std::string generate_use_state_hooks(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// useState hooks\n";
    for (const auto& field : component_def.fields) {
        if (field.attributes.find("state") != field.attributes.end()) {
            std::string ts_type = cpp_to_typescript(field.type);
            std::string default_value = get_default_value(field.type);
            
            oss << "const [" << field.name << ", set" 
                << capitalize(field.name) << "] = useState<" << ts_type 
                << ">(" << default_value << ");\n";
        }
    }
    oss << "\n";
    
    return oss.str();
}

// Generate useEffect hooks
std::string generate_use_effect_hooks(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// useEffect hooks\n";
    int effect_count = 0;
    for (const auto& func : component_def.functions) {
        if (func.attributes.find("effect") != func.attributes.end()) {
            std::string deps = extract_dependencies(func);
            
            oss << "useEffect(() => {\n";
            oss << "  " << func.name << "();\n";
            oss << "}, [" << deps << "]);\n\n";
            
            effect_count++;
        }
    }
    
    if (effect_count == 0) {
        oss << "// No effects found\n\n";
    }
    
    return oss.str();
}

// Generate useRef hooks
std::string generate_use_ref_hooks(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// useRef hooks\n";
    for (const auto& field : component_def.fields) {
        if (field.type.name.find("Ref") != std::string::npos ||
            field.attributes.find("ref") != field.attributes.end()) {
            std::string ts_type = cpp_to_typescript(field.type);
            
            oss << "const " << field.name << "Ref = useRef<" << ts_type 
                << ">(null);\n";
        }
    }
    oss << "\n";
    
    return oss.str();
}

// Generate useCallback hooks
std::string generate_use_callback_hooks(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// useCallback hooks\n";
    for (const auto& field : component_def.fields) {
        if (field.type.name.find("function") != std::string::npos ||
            field.type.name.find("callback") != std::string::npos) {
            std::string ts_type = cpp_to_typescript(field.type);
            std::string deps = extract_callback_dependencies(field);
            
            oss << "const " << field.name << "Callback = useCallback<" 
                << ts_type << ">(\n";
            oss << "  " << field.name << ",\n";
            oss << "  [" << deps << "]\n";
            oss << ");\n\n";
        }
    }
    
    return oss.str();
}

// Generate useMemo hooks
std::string generate_use_memo_hooks(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// useMemo hooks\n";
    for (const auto& func : component_def.functions) {
        if (func.attributes.find("memo") != func.attributes.end()) {
            std::string deps = extract_dependencies(func);
            std::string ts_return = cpp_to_typescript(func.return_type);
            
            oss << "const " << func.name << "Memo = useMemo<" << ts_return << ">(() => {\n";
            oss << "  return " << func.name << "();\n";
            oss << "}, [" << deps << "]);\n\n";
        }
    }
    
    return oss.str();
}

// Helper: Extract dependencies from function
std::string extract_dependencies(const CppFunction& func) {
    std::vector<std::string> deps;
    for (const auto& param : func.parameters) {
        deps.push_back(param.name);
    }
    
    if (deps.empty()) {
        return "";
    }
    
    std::ostringstream oss;
    for (size_t i = 0; i < deps.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << deps[i];
    }
    return oss.str();
}

// Helper: Extract callback dependencies
std::string extract_callback_dependencies(const CppField& field) {
    // Extract from field attributes or infer from type
    auto it = field.attributes.find("deps");
    if (it != field.attributes.end()) {
        return it->second;
    }
    return "";
}

// Helper: Get default value for type
std::string get_default_value(const CppType& type) {
    if (type.name == "int" || type.name == "std::int32_t") {
        return "0";
    } else if (type.name == "double" || type.name == "float") {
        return "0.0";
    } else if (type.name == "bool") {
        return "false";
    } else if (type.name == "std::string" || type.name == "string") {
        return "\"\"";
    } else if (type.name.find("vector") != std::string::npos ||
               type.name.find("Array") != std::string::npos) {
        return "[]";
    } else if (type.name.find("optional") != std::string::npos ||
               type.name.find("Maybe") != std::string::npos) {
        return "null";
    }
    return "null";
}

// Helper: Capitalize string
std::string capitalize(const std::string& str) {
    if (str.empty()) return str;
    std::string result = str;
    result[0] = std::toupper(result[0]);
    return result;
}

} // namespace react_hooks_generator
