// React Server Components Support - Phase 4
#include "ServerComponents.h"
#include "Cpp23Parser.h"
#include <string>
#include <sstream>

namespace server_components {

// Generate Server Component
std::string generate_server_component(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// Server Component: " << component_def.name << "\n";
    oss << "'use client';\n\n";  // Next.js directive (or remove for pure server)
    
    oss << "import { ReactNode } from 'react';\n\n";
    
    // Generate async server component
    oss << "interface " << component_def.name << "Props {\n";
    for (const auto& field : component_def.fields) {
        std::string ts_type = cpp_to_typescript(field.type);
        std::string optional = field.is_optional ? "?" : "";
        oss << "  " << field.name << optional << ": " << ts_type << ";\n";
    }
    oss << "}\n\n";
    
    oss << "export async function " << component_def.name 
        << "(props: " << component_def.name << "Props) {\n";
    
    // Generate server-side data fetching if needed
    bool has_async_operations = false;
    for (const auto& func : component_def.functions) {
        if (func.attributes.find("server") != func.attributes.end() ||
            func.attributes.find("async") != func.attributes.end()) {
            has_async_operations = true;
            oss << "  const " << func.name << "Result = await " 
                << func.name << "();\n";
        }
    }
    
    if (!has_async_operations) {
        oss << "  // Server component logic\n";
    }
    
    oss << "\n";
    oss << "  return (\n";
    oss << "    <div>\n";
    
    // Render fields
    for (const auto& field : component_def.fields) {
        if (field.type.name == "std::string" || 
            cpp_to_typescript(field.type) == "string") {
            oss << "      <p>{props." << field.name << "}</p>\n";
        }
    }
    
    oss << "    </div>\n";
    oss << "  );\n";
    oss << "}\n";
    
    return oss.str();
}

// Generate Server Component with streaming
std::string generate_streaming_server_component(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// Streaming Server Component: " << component_def.name << "\n";
    oss << "import { Suspense } from 'react';\n\n";
    
    oss << generate_server_component(component_def);
    
    oss << "\n// Streaming wrapper\n";
    oss << "export function " << component_def.name 
        << "Streaming(props: " << component_def.name << "Props) {\n";
    oss << "  return (\n";
    oss << "    <Suspense fallback={<div>Loading...</div>}>\n";
    oss << "      <" << component_def.name << " {...props} />\n";
    oss << "    </Suspense>\n";
    oss << "  );\n";
    oss << "}\n";
    
    return oss.str();
}

// Generate Server Action
std::string generate_server_action(const CppFunction& func) {
    std::ostringstream oss;
    
    oss << "// Server Action: " << func.name << "\n";
    oss << "'use server';\n\n";
    
    oss << "import { revalidatePath, revalidateTag } from 'next/cache';\n\n";
    
    // Generate action function
    std::string ts_return = cpp_to_typescript(func.return_type);
    
    oss << "export async function " << func.name << "(";
    for (size_t i = 0; i < func.parameters.size(); ++i) {
        if (i > 0) oss << ", ";
        std::string ts_type = cpp_to_typescript(func.parameters[i].type);
        oss << func.parameters[i].name << ": " << ts_type;
    }
    oss << "): Promise<" << ts_return << "> {\n";
    
    // Check for revalidation attributes
    bool has_revalidate = func.attributes.find("revalidate") != func.attributes.end();
    if (has_revalidate) {
        auto it = func.attributes.find("revalidate");
        oss << "  revalidatePath('" << it->second << "');\n";
    }
    
    oss << "  // Server action implementation\n";
    oss << "  return /* result */;\n";
    oss << "}\n";
    
    return oss.str();
}

// Generate form action
std::string generate_form_action(const CppFunction& func) {
    std::ostringstream oss;
    
    oss << "// Form Action: " << func.name << "\n";
    oss << "'use server';\n\n";
    
    oss << "export async function " << func.name << "Action(formData: FormData) {\n";
    oss << "  // Extract form data\n";
    
    for (const auto& param : func.parameters) {
        oss << "  const " << param.name << " = formData.get('" 
            << param.name << "') as string;\n";
    }
    
    oss << "\n";
    oss << "  // Process form action\n";
    oss << "  await " << func.name << "(";
    for (size_t i = 0; i < func.parameters.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << func.parameters[i].name;
    }
    oss << ");\n";
    
    oss << "\n";
    oss << "  revalidatePath('/');\n";
    oss << "  redirect('/success');\n";
    oss << "}\n";
    
    return oss.str();
}

// Helper functions
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

} // namespace server_components
