// C++23 Parser using Clang libTooling
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/Type.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Tooling/CommonOptionsParser.h>
#include <clang/Tooling/Tooling.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <string>
#include <vector>
#include <map>

using namespace clang;

// C++23 AST representation
struct CppStruct {
    std::string name;
    std::vector<CppField> fields;
    bool is_component = false;
    std::string radix_component;
    std::vector<std::string> styles;
};

struct CppField {
    std::string name;
    CppType type;
    bool is_optional = false;
};

struct CppType {
    std::string name;
    std::vector<CppType> template_args;
    bool is_const = false;
    bool is_reference = false;
    bool is_pointer = false;
};

struct CppFunction {
    std::string name;
    CppType return_type;
    std::vector<std::pair<std::string, CppType>> parameters;
    bool is_component_factory = false;
};

// AST Visitor to extract component information
class ComponentVisitor : public RecursiveASTVisitor<ComponentVisitor> {
public:
    explicit ComponentVisitor(ASTContext* context) : context_(context) {}
    
    bool VisitCXXRecordDecl(CXXRecordDecl* decl) {
        if (!decl->isStruct() && !decl->isClass()) {
            return true;
        }
        
        CppStruct struct_def;
        struct_def.name = decl->getNameAsString();
        
        // Check for [[react_component]] attribute
        for (const auto* attr : decl->attrs()) {
            if (auto annot = dyn_cast<AnnotateAttr>(attr)) {
                std::string annotation = annot->getAnnotation().str();
                if (annotation == "react_component") {
                    struct_def.is_component = true;
                } else if (annotation.find("radix_component") != std::string::npos) {
                    // Extract Radix component name
                    size_t start = annotation.find("(");
                    size_t end = annotation.find(")");
                    if (start != std::string::npos && end != std::string::npos) {
                        struct_def.radix_component = annotation.substr(start + 1, end - start - 1);
                    }
                }
            }
        }
        
        // Extract fields
        for (const auto* field : decl->fields()) {
            CppField f;
            f.name = field->getNameAsString();
            f.type = typeToCppType(field->getType());
            struct_def.fields.push_back(f);
        }
        
        components_.push_back(struct_def);
        return true;
    }
    
    bool VisitFunctionDecl(FunctionDecl* decl) {
        if (!decl->isCXXInstanceMember()) {
            CppFunction func;
            func.name = decl->getNameAsString();
            func.return_type = typeToCppType(decl->getReturnType());
            
            for (unsigned i = 0; i < decl->getNumParams(); ++i) {
                ParmVarDecl* param = decl->getParamDecl(i);
                func.parameters.push_back({
                    param->getNameAsString(),
                    typeToCppType(param->getType())
                });
            }
            
            // Check for [[react_component_factory]] attribute
            for (const auto* attr : decl->attrs()) {
                if (auto annot = dyn_cast<AnnotateAttr>(attr)) {
                    if (annot->getAnnotation() == "react_component_factory") {
                        func.is_component_factory = true;
                    }
                }
            }
            
            functions_.push_back(func);
        }
        return true;
    }
    
    std::vector<CppStruct> getComponents() const { return components_; }
    std::vector<CppFunction> getFunctions() const { return functions_; }
    
private:
    ASTContext* context_;
    std::vector<CppStruct> components_;
    std::vector<CppFunction> functions_;
    
    CppType typeToCppType(QualType qt) {
        CppType type;
        const Type* t = qt.getTypePtr();
        
        type.is_const = qt.isConstQualified();
        type.is_reference = qt->isReferenceType();
        type.is_pointer = qt->isPointerType();
        
        if (auto* builtin = dyn_cast<BuiltinType>(t)) {
            type.name = builtinTypeToString(builtin);
        } else if (auto* record = dyn_cast<RecordType>(t)) {
            type.name = record->getDecl()->getNameAsString();
        } else if (auto* template = dyn_cast<TemplateSpecializationType>(t)) {
            type.name = template->getTemplateName().getAsTemplateDecl()->getNameAsString();
            for (unsigned i = 0; i < template->getNumArgs(); ++i) {
                const TemplateArgument& arg = template->getArg(i);
                if (arg.getKind() == TemplateArgument::Type) {
                    type.template_args.push_back(typeToCppType(arg.getAsType()));
                }
            }
        } else {
            type.name = qt.getAsString();
        }
        
        return type;
    }
    
    std::string builtinTypeToString(const BuiltinType* bt) {
        switch (bt->getKind()) {
            case BuiltinType::Int: return "int";
            case BuiltinType::Long: return "long";
            case BuiltinType::LongLong: return "long long";
            case BuiltinType::Float: return "float";
            case BuiltinType::Double: return "double";
            case BuiltinType::Bool: return "bool";
            case BuiltinType::Char_S: return "char";
            default: return "unknown";
        }
    }
};

// Frontend action to run visitor
class ComponentExtractionAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance& CI, StringRef file) override {
        return std::make_unique<ComponentExtractionConsumer>(&CI.getASTContext());
    }
    
private:
    class ComponentExtractionConsumer : public ASTConsumer {
    public:
        explicit ComponentExtractionConsumer(ASTContext* context) : visitor_(context) {}
        
        void HandleTranslationUnit(ASTContext& context) override {
            visitor_.TraverseDecl(context.getTranslationUnitDecl());
            components_ = visitor_.getComponents();
            functions_ = visitor_.getFunctions();
        }
        
        std::vector<CppStruct> getComponents() const { return components_; }
        std::vector<CppFunction> getFunctions() const { return functions_; }
        
    private:
        ComponentVisitor visitor_;
        std::vector<CppStruct> components_;
        std::vector<CppFunction> functions_;
    };
};

// Parse C++23 file and extract components
std::vector<CppStruct> parseCpp23File(const std::string& filename) {
    std::vector<std::string> args = {
        "-std=c++23",
        "-I/usr/include",
        "-I/usr/local/include"
    };
    
    clang::tooling::FixedCompilationDatabase compilations(".", args);
    clang::tooling::ClangTool tool(compilations, {filename});
    
    std::vector<CppStruct> components;
    
    tool.run(clang::tooling::newFrontendActionFactory<ComponentExtractionAction>().get());
    
    return components;
}
