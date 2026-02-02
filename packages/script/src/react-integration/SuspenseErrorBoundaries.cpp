// Suspense and Error Boundaries - Phase 4
#include "SuspenseErrorBoundaries.h"
#include "Cpp23Parser.h"
#include <string>
#include <sstream>

namespace suspense_error_boundaries {

// Generate Error Boundary component
std::string generate_error_boundary(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// Error Boundary for " << component_def.name << "\n";
    oss << "import { Component, ReactNode, ErrorInfo } from 'react';\n\n";
    
    oss << "interface " << component_def.name << "ErrorBoundaryProps {\n";
    oss << "  children: ReactNode;\n";
    oss << "  fallback?: ReactNode;\n";
    oss << "  onError?: (error: Error, errorInfo: ErrorInfo) => void;\n";
    oss << "}\n\n";
    
    oss << "interface " << component_def.name << "ErrorBoundaryState {\n";
    oss << "  hasError: boolean;\n";
    oss << "  error: Error | null;\n";
    oss << "}\n\n";
    
    oss << "export class " << component_def.name 
        << "ErrorBoundary extends Component<\n";
    oss << "  " << component_def.name << "ErrorBoundaryProps,\n";
    oss << "  " << component_def.name << "ErrorBoundaryState\n";
    oss << "> {\n";
    
    oss << "  constructor(props: " << component_def.name 
        << "ErrorBoundaryProps) {\n";
    oss << "    super(props);\n";
    oss << "    this.state = { hasError: false, error: null };\n";
    oss << "  }\n\n";
    
    oss << "  static getDerivedStateFromError(error: Error): " 
        << component_def.name << "ErrorBoundaryState {\n";
    oss << "    return { hasError: true, error };\n";
    oss << "  }\n\n";
    
    oss << "  componentDidCatch(error: Error, errorInfo: ErrorInfo) {\n";
    oss << "    if (this.props.onError) {\n";
    oss << "      this.props.onError(error, errorInfo);\n";
    oss << "    }\n";
    oss << "    console.error('Error caught by boundary:', error, errorInfo);\n";
    oss << "  }\n\n";
    
    oss << "  render() {\n";
    oss << "    if (this.state.hasError) {\n";
    oss << "      if (this.props.fallback) {\n";
    oss << "        return this.props.fallback;\n";
    oss << "      }\n";
    oss << "      return (\n";
    oss << "        <div className=\"error-boundary\">\n";
    oss << "          <h2>Something went wrong</h2>\n";
    oss << "          <p>{this.state.error?.message}</p>\n";
    oss << "        </div>\n";
    oss << "      );\n";
    oss << "    }\n\n";
    oss << "    return this.props.children;\n";
    oss << "  }\n";
    oss << "}\n";
    
    return oss.str();
}

// Generate Suspense wrapper
std::string generate_suspense_wrapper(const CppStruct& component_def) {
    std::ostringstream oss;
    
    oss << "// Suspense wrapper for " << component_def.name << "\n";
    oss << "import { Suspense, ReactNode } from 'react';\n\n";
    
    oss << "interface " << component_def.name << "SuspenseProps {\n";
    oss << "  children: ReactNode;\n";
    oss << "  fallback?: ReactNode;\n";
    oss << "}\n\n";
    
    oss << "export const " << component_def.name 
        << "Suspense: React.FC<" << component_def.name 
        << "SuspenseProps> = ({ children, fallback }) => {\n";
    oss << "  return (\n";
    oss << "    <Suspense fallback={fallback || <div>Loading...</div>}>\n";
    oss << "      {children}\n";
    oss << "    </Suspense>\n";
    oss << "  );\n";
    oss << "};\n";
    
    return oss.str();
}

// Generate async component with Suspense
std::string generate_async_component(const CppFunction& async_func) {
    std::ostringstream oss;
    
    oss << "// Async component from " << async_func.name << "\n";
    oss << "import { use, Suspense } from 'react';\n\n";
    
    oss << "interface " << async_func.name << "Props {\n";
    for (const auto& param : async_func.parameters) {
        std::string ts_type = cpp_to_typescript(param.type);
        oss << "  " << param.name << ": " << ts_type << ";\n";
    }
    oss << "}\n\n";
    
    oss << "async function " << async_func.name << "Component(props: " 
        << async_func.name << "Props) {\n";
    oss << "  const data = await " << async_func.name << "(";
    
    for (size_t i = 0; i < async_func.parameters.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << "props." << async_func.parameters[i].name;
    }
    oss << ");\n\n";
    
    oss << "  return (\n";
    oss << "    <div>\n";
    oss << "      {/* Rendered data */}\n";
    oss << "    </div>\n";
    oss << "  );\n";
    oss << "}\n\n";
    
    oss << "export const " << async_func.name 
        << ": React.FC<" << async_func.name << "Props> = (props) => {\n";
    oss << "  return (\n";
    oss << "    <Suspense fallback={<div>Loading...</div>}>\n";
    oss << "      <" << async_func.name << "Component {...props} />\n";
    oss << "    </Suspense>\n";
    oss << "  );\n";
    oss << "};\n";
    
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

} // namespace suspense_error_boundaries
