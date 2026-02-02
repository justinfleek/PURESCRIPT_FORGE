// State Management Integration (Redux/Zustand) - Phase 4
#include "StateManagement.h"
#include "Cpp23Parser.h"
#include <string>
#include <sstream>
#include <vector>
#include <map>

namespace state_management {

// Generate Redux store and actions
std::string generate_redux_store(const CppStruct& state_def) {
    std::ostringstream oss;
    
    oss << "// Redux Store for " << state_def.name << "\n";
    oss << "import { createSlice, configureStore } from '@reduxjs/toolkit';\n\n";
    
    // Generate initial state
    oss << "const initialState: " << state_def.name << "State = {\n";
    for (const auto& field : state_def.fields) {
        std::string default_val = get_default_value(field.type);
        oss << "  " << field.name << ": " << default_val << ",\n";
    }
    oss << "};\n\n";
    
    // Generate slice
    oss << "const " << state_def.name << "Slice = createSlice({\n";
    oss << "  name: '" << state_def.name << "',\n";
    oss << "  initialState,\n";
    oss << "  reducers: {\n";
    
    // Generate reducers for each field
    for (const auto& field : state_def.fields) {
        oss << "    set" << capitalize(field.name) << ": (state, action) => {\n";
        oss << "      state." << field.name << " = action.payload;\n";
        oss << "    },\n";
    }
    
    oss << "  },\n";
    oss << "});\n\n";
    
    // Export actions and reducer
    oss << "export const { ";
    for (size_t i = 0; i < state_def.fields.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << "set" << capitalize(state_def.fields[i].name);
    }
    oss << " } = " << state_def.name << "Slice.actions;\n\n";
    
    oss << "export default " << state_def.name << "Slice.reducer;\n";
    
    return oss.str();
}

// Generate Zustand store
std::string generate_zustand_store(const CppStruct& state_def) {
    std::ostringstream oss;
    
    oss << "// Zustand Store for " << state_def.name << "\n";
    oss << "import { create } from 'zustand';\n";
    oss << "import { devtools } from 'zustand/middleware';\n\n";
    
    // Generate state interface
    oss << "interface " << state_def.name << "State {\n";
    for (const auto& field : state_def.fields) {
        std::string ts_type = cpp_to_typescript(field.type);
        oss << "  " << field.name << ": " << ts_type << ";\n";
    }
    
    // Generate actions interface
    oss << "}\n\n";
    oss << "interface " << state_def.name << "Actions {\n";
    for (const auto& field : state_def.fields) {
        std::string ts_type = cpp_to_typescript(field.type);
        oss << "  set" << capitalize(field.name) 
            << ": (" << field.name << ": " << ts_type << ") => void;\n";
    }
    oss << "}\n\n";
    
    // Generate store
    oss << "export const use" << state_def.name << "Store = create<" 
        << state_def.name << "State & " << state_def.name << "Actions>()(\n";
    oss << "  devtools(\n";
    oss << "    (set) => ({\n";
    
    // Initial state
    for (const auto& field : state_def.fields) {
        std::string default_val = get_default_value(field.type);
        oss << "      " << field.name << ": " << default_val << ",\n";
    }
    
    // Actions
    for (const auto& field : state_def.fields) {
        oss << "      set" << capitalize(field.name) << ": (" << field.name 
            << ") => set({ " << field.name << " }),\n";
    }
    
    oss << "    }),\n";
    oss << "    { name: '" << state_def.name << "Store' }\n";
    oss << "  )\n";
    oss << ");\n";
    
    return oss.str();
}

// Generate React hooks for state management
std::string generate_state_hooks(const CppStruct& state_def, 
                                 const std::string& store_type) {
    std::ostringstream oss;
    
    if (store_type == "redux") {
        oss << "// Redux hooks\n";
        oss << "import { useSelector, useDispatch } from 'react-redux';\n\n";
        
        for (const auto& field : state_def.fields) {
            oss << "export const use" << capitalize(field.name) << " = () => {\n";
            oss << "  const " << field.name << " = useSelector((state: RootState) => "
                << "state." << state_def.name << "." << field.name << ");\n";
            oss << "  const dispatch = useDispatch();\n";
            oss << "  const set" << capitalize(field.name) << " = (" << field.name 
                << ": " << cpp_to_typescript(field.type) << ") => {\n";
            oss << "    dispatch(set" << capitalize(field.name) << "(" << field.name << "));\n";
            oss << "  };\n";
            oss << "  return [" << field.name << ", set" 
                << capitalize(field.name) << "] as const;\n";
            oss << "};\n\n";
        }
    } else if (store_type == "zustand") {
        oss << "// Zustand hooks (already generated in store)\n";
        oss << "// Use: const { " << state_def.fields[0].name;
        for (size_t i = 1; i < state_def.fields.size(); ++i) {
            oss << ", " << state_def.fields[i].name;
        }
        oss << " } = use" << state_def.name << "Store();\n";
    }
    
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

std::string capitalize(const std::string& str) {
    if (str.empty()) return str;
    std::string result = str;
    result[0] = std::toupper(result[0]);
    return result;
}

std::string cpp_to_typescript(const CppType& type) {
    // Type conversion (simplified - would use full implementation)
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

} // namespace state_management
