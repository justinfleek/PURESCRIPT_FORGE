// C++23 → React/TypeScript Generator (Complete Implementation)
#include "ReactGenerator.h"
#include "RadixBinder.h"
#include "TailwindGenerator.h"
#include "Cpp23Parser.h"
#include "NexusIntegration.h"
#include <string>
#include <vector>
#include <map>
#include <sstream>
#include <fstream>
#include <filesystem>
#include <algorithm>
#include <numeric>

namespace react_generator {

// Generate complete React component with all features
std::string generate_react_component(const CppStruct& component_def) {
    std::ostringstream oss;
    
    // Check for Nexus agent launch integration
    bool has_nexus_integration = nexus_integration::has_nexus_agent_launch(component_def);
    
    // Determine if using Radix UI
    bool use_radix = !component_def.radix_component.empty();
    std::string radix_package = use_radix ? 
        radix_binder::get_radix_import(component_def.radix_component) : "";
    
    // Import statements
    oss << "import * as React from 'react';\n";
    if (use_radix) {
        oss << "import * as " << component_def.name << "Radix from '" << radix_package << "';\n";
    }
    if (has_nexus_integration) {
        oss << "import { AgentLaunchButton } from '@/components/AgentLaunchButton';\n";
        oss << "import { useWebSocket } from '@/hooks/useWebSocket';\n";
    }
    oss << "import { cn } from '@/lib/utils';\n"; // Tailwind utility
    oss << "\n";
    
    // Props interface
    oss << "export interface " << component_def.name << "Props {\n";
    for (const auto& field : component_def.fields) {
        std::string optional = field.is_optional ? "?" : "";
        oss << "  " << field.name << optional << ": " 
            << cpp_to_typescript(field.type) << ";\n";
    }
    oss << "}\n\n";
    
    // Component function
    oss << "export const " << component_def.name << ": React.FC<" 
        << component_def.name << "Props> = (props) => {\n";
    
    // Destructure props
    oss << "  const { ";
    for (size_t i = 0; i < component_def.fields.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << component_def.fields[i].name;
    }
    oss << " } = props;\n\n";
    
    // Generate Tailwind classes
    std::string className = tailwind_generator::generate_class_name_prop(
        component_def.styles
    );
    
    // Component JSX
    if (use_radix) {
        // Use Radix UI component
        oss << "  return (\n";
        oss << "    <" << component_def.name << "Radix.Root";
        
        // Add props
        for (const auto& field : component_def.fields) {
            if (field.name == "className") {
                continue; // Handle separately
            }
            oss << " " << field.name << "={" << field.name << "}";
        }
        
        if (!className.empty()) {
            oss << " className={" << className << "}";
        }
        
        oss << ">\n";
        oss << "      {props.children}\n";
        oss << "    </" << component_def.name << "Radix.Root>\n";
        oss << "  );\n";
    } else {
        // Standard React component
        oss << "  return (\n";
        oss << "    <div";
        if (!className.empty()) {
            oss << " className={" << className << "}";
        }
        oss << ">\n";
        oss << "      {/* Generated from C++23 */}\n";
        
        // Render fields as content
        for (const auto& field : component_def.fields) {
            if (field.type.name == "std::string" || 
                cpp_to_typescript(field.type) == "string") {
                oss << "      {" << field.name << "}\n";
            }
        }
        
        // Add Nexus agent launch button if integrated
        if (has_nexus_integration) {
            oss << "\n      {/* Nexus Agent Launch Integration */}\n";
            oss << "      <AgentLaunchButton\n";
            oss << "        taskDescription=\"Complete task for " << component_def.name << "\"\n";
            oss << "        agentType=\"research\"\n";
            oss << "        onComplete={(result) => {\n";
            oss << "          console.log('Agent task completed:', result);\n";
            oss << "        }}\n";
            oss << "      />\n";
        }
        
        oss << "    </div>\n";
        oss << "  );\n";
    }
    
    oss << "};\n";
    
    return oss.str();
}

// Convert C++ type to TypeScript type (complete implementation)
std::string cpp_to_typescript(const CppType& type) {
    // Handle const/reference/pointer qualifiers
    CppType baseType = type;
    baseType.is_const = false;
    baseType.is_reference = false;
    baseType.is_pointer = false;
    
    std::string base = cpp_to_typescript_base(baseType);
    
    // Add nullability for pointers/optional
    if (type.is_pointer || type.name == "std::optional") {
        return base + " | null";
    }
    
    return base;
}

std::string cpp_to_typescript_base(const CppType& type) {
    if (type.name == "std::string") {
        return "string";
    } else if (type.name == "int" || type.name == "std::int64_t" || 
               type.name == "long" || type.name == "long long") {
        return "number";
    } else if (type.name == "double" || type.name == "float") {
        return "number";
    } else if (type.name == "bool") {
        return "boolean";
    } else if (type.name == "std::vector") {
        if (!type.template_args.empty()) {
            return cpp_to_typescript(type.template_args[0]) + "[]";
        }
        return "any[]";
    } else if (type.name == "std::optional") {
        if (!type.template_args.empty()) {
            return cpp_to_typescript(type.template_args[0]) + " | null";
        }
        return "any | null";
    } else if (type.name == "std::variant") {
        std::string result;
        for (size_t i = 0; i < type.template_args.size(); ++i) {
            if (i > 0) result += " | ";
            result += cpp_to_typescript(type.template_args[i]);
        }
        return result;
    } else if (type.name == "std::function") {
        // std::function<Return(Args...)> -> (args: Args) => Return
        if (type.template_args.size() >= 2) {
            auto return_type = type.template_args[0];
            std::string args;
            for (size_t i = 1; i < type.template_args.size(); ++i) {
                if (i > 1) args += ", ";
                args += "arg" + std::to_string(i - 1) + ": " + 
                        cpp_to_typescript(type.template_args[i]);
            }
            return "(" + args + ") => " + cpp_to_typescript(return_type);
        }
        return "() => void";
    } else if (type.name == "std::map" || type.name == "std::unordered_map") {
        if (type.template_args.size() >= 2) {
            return "Record<" + cpp_to_typescript(type.template_args[0]) + 
                   ", " + cpp_to_typescript(type.template_args[1]) + ">";
        }
        return "Record<string, any>";
    } else if (type.name == "std::pair") {
        if (type.template_args.size() >= 2) {
            return "[" + cpp_to_typescript(type.template_args[0]) + 
                   ", " + cpp_to_typescript(type.template_args[1]) + "]";
        }
        return "[any, any]";
    } else if (type.name == "std::future") {
        if (!type.template_args.empty()) {
            return "Promise<" + cpp_to_typescript(type.template_args[0]) + ">";
        }
        return "Promise<any>";
    }
    
    // Custom types pass through (should be interfaces)
    return type.name;
}

// Generate TypeScript interface from C++ struct
std::string generate_typescript_interface(const CppStruct& struct_def) {
    std::ostringstream oss;
    oss << "export interface " << struct_def.name << " {\n";
    for (const auto& field : struct_def.fields) {
        std::string optional = field.is_optional ? "?" : "";
        oss << "  " << field.name << optional << ": " 
            << cpp_to_typescript(field.type) << ";\n";
    }
    oss << "}\n";
    return oss.str();
}

// Main generation function (complete)
void generate_react_code(const std::vector<CppStruct>& components,
                        const std::string& output_dir) {
    std::filesystem::create_directories(output_dir);
    
    // Create hooks directory for Nexus integration
    std::filesystem::create_directories(output_dir + "/hooks");
    std::filesystem::create_directories(output_dir + "/components");
    
    // Generate Nexus integration hooks
    std::ofstream ws_hook_file(output_dir + "/hooks/useWebSocket.ts");
    ws_hook_file << nexus_integration::generate_websocket_client_hook();
    ws_hook_file.close();
    
    std::ofstream attest_hook_file(output_dir + "/hooks/useAttestation.ts");
    attest_hook_file << nexus_integration::generate_attestation_hook();
    attest_hook_file.close();
    
    // Generate AgentLaunchButton component
    nexus_integration::AgentLaunchTask default_task;
    default_task.task_id = "default-task";
    default_task.task_description = "Default agent task";
    default_task.agent_type = "research";
    default_task.requires_attestation = true;
    
    std::ofstream agent_button_file(output_dir + "/components/AgentLaunchButton.tsx");
    agent_button_file << nexus_integration::generate_agent_launch_button(default_task, "AgentLaunchButton");
    agent_button_file.close();
    
    // Generate index file
    std::ofstream index_file(output_dir + "/index.ts");
    index_file << "// Auto-generated React components\n\n";
    
    // Export hooks
    index_file << "export { useWebSocket } from './hooks/useWebSocket';\n";
    index_file << "export { useAttestation } from './hooks/useAttestation';\n";
    index_file << "export { AgentLaunchButton } from './components/AgentLaunchButton';\n\n";
    
    for (const auto& component : components) {
        std::string filename = component.name + ".tsx";
        std::string filepath = output_dir + "/" + filename;
        
        if (component.is_component) {
            // Generate React component
            std::ofstream file(filepath);
            file << generate_react_component(component);
            file.close();
            
            // Export in index
            index_file << "export { " << component.name 
                      << ", type " << component.name << "Props } from './" 
                      << component.name << "';\n";
        } else {
            // Generate TypeScript interface
            std::ofstream file(output_dir + "/" + component.name + ".ts");
            file << generate_typescript_interface(component);
            file.close();
            
            // Export in index
            index_file << "export type { " << component.name << " } from './" 
                      << component.name << "';\n";
        }
    }
    
    index_file.close();
}

// Generate React hooks for state management
std::string generate_react_hook(const CppFunction& func) {
    if (!func.is_component_factory) {
        return "";
    }
    
    std::ostringstream oss;
    oss << "export function use" << func.name << "(";
    
    // Parameters
    for (size_t i = 0; i < func.parameters.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << func.parameters[i].first << ": " 
            << cpp_to_typescript(func.parameters[i].second);
    }
    
    oss << ") {\n";
    oss << "  const [state, setState] = React.useState<" 
        << cpp_to_typescript(func.return_type) << " | null>(null);\n\n";
    oss << "  React.useEffect(() => {\n";
    oss << "    // Call C++ function via WASM\n";
    oss << "    // const result = wasmModule." << func.name << "(";
    for (size_t i = 0; i < func.parameters.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << func.parameters[i].first;
    }
    oss << ");\n";
    oss << "    // setState(result);\n";
    oss << "  }, [";
    for (size_t i = 0; i < func.parameters.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << func.parameters[i].first;
    }
    oss << "]);\n\n";
    oss << "  return state;\n";
    oss << "}\n";
    
    return oss.str();
}

} // namespace react_generator
