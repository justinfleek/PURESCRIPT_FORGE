{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Cpp23Generator where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.List as L
import Parser
import TypeChecker

-- | Generate complete C++23 header file
generateCpp23Header :: PSModule -> T.Text
generateCpp23Header PSModule{..} = T.unlines
  [ "#pragma once"
  , ""
  , "#include <string>"
  , "#include <vector>"
  , "#include <optional>"
  , "#include <variant>"
  , "#include <functional>"
  , "#include <future>"
  , "#include <concepts>"
  , "#include <memory>"
  , "#include <map>"
  , "#include <unordered_map>"
  , ""
  , "namespace " <> toCppNamespace moduleName <> " {"
  , ""
  , T.unlines (map generateForwardDecl (filter isDataOrType moduleDeclarations))
  , ""
  , T.unlines (map generateDeclaration moduleDeclarations)
  , ""
  , "} // namespace " <> toCppNamespace moduleName
  ]

-- | Generate complete C++23 implementation file
generateCpp23Impl :: PSModule -> T.Text
generateCpp23Impl PSModule{..} = T.unlines
  [ "#include \"" <> toCppHeaderName moduleName <> ".hpp\""
  , ""
  , "namespace " <> toCppNamespace moduleName <> " {"
  , ""
  , T.unlines (map generateImplementation moduleDeclarations)
  , ""
  , "} // namespace " <> toCppNamespace moduleName
  ]

isDataOrType :: PSDeclaration -> Bool
isDataOrType (PSDataDecl _) = True
isDataOrType (PSTypeDecl _) = True
isDataOrType _ = False

generateForwardDecl :: PSDeclaration -> T.Text
generateForwardDecl (PSDataDecl PSDataDeclaration{..}) =
  "struct " <> dataName <> generateTemplateParams dataTypeVars <> ";"
generateForwardDecl (PSTypeDecl PSTypeDeclaration{..}) =
  "using " <> typeName <> generateTemplateParams typeVars <> " = " <> toCppType typeDefinition <> ";"
generateForwardDecl _ = ""

toCppHeaderName :: T.Text -> T.Text
toCppHeaderName = T.replace "." "_"

-- | Convert PureScript module name to C++ namespace
toCppNamespace :: T.Text -> T.Text
toCppNamespace = T.replace "." "_"

-- | Generate C++ import/include
generateImport :: PSImport -> T.Text
generateImport PSImport{..} = 
  if importQualified
    then "#include \"" <> importModule <> ".hpp\"  // qualified as " <> maybe "" id importAs
    else "#include \"" <> importModule <> ".hpp\""

-- | Generate C++ declaration from PureScript declaration
generateDeclaration :: PSDeclaration -> T.Text
generateDeclaration (PSDataDecl decl) = generateDataDecl decl
generateDeclaration (PSTypeDecl decl) = generateTypeDecl decl
generateDeclaration (PSValueDecl decl) = generateValueDecl decl
generateDeclaration (PSClassDecl decl) = generateClassDecl decl
generateDeclaration (PSInstanceDecl decl) = generateInstanceDecl decl

-- | Generate C++ struct/enum from PureScript data declaration
generateDataDecl :: PSDataDeclaration -> T.Text
generateDataDecl PSDataDeclaration{..} =
  if length dataConstructors == 1 && null (constructorArgs (head dataConstructors))
    then generateTypeAlias dataName dataTypeVars (head dataConstructors)
    else if length dataConstructors == 1
    then generateStruct dataName dataTypeVars (head dataConstructors)
    else generateEnum dataName dataTypeVars dataConstructors

generateTypeAlias :: T.Text -> [T.Text] -> PSConstructor -> T.Text
generateTypeAlias name vars PSConstructor{..} =
  "using " <> name <> generateTemplateParams vars <> " = " <> constructorName <> ";"

generateStruct :: T.Text -> [T.Text] -> PSConstructor -> T.Text
generateStruct name vars PSConstructor{..} =
  T.unlines
    [ "struct " <> name <> generateTemplateParams vars <> " {"
    , T.unlines (zipWith generateField [0..] constructorArgs)
    , ""
    , "  // Constructor"
    , "  " <> name <> "(" <> T.intercalate ", " (zipWith (\i t -> toCppType t <> " arg" <> T.pack (show i)) [0..] constructorArgs) <> ")"
    , "    : " <> T.intercalate "\n    , " (zipWith (\i _ -> "field" <> T.pack (show i) <> "(arg" <> T.pack (show i) <> ")") [0..] constructorArgs) <> " {}"
    , "};"
    ]
  where
    generateField i typ = "  " <> toCppType typ <> " field" <> T.pack (show i) <> ";"

generateEnum :: T.Text -> [T.Text] -> [PSConstructor] -> T.Text
generateEnum name vars constructors =
  T.unlines
    [ "enum class " <> name <> generateTemplateParams vars <> " {"
    , T.intercalate ",\n" (map (\(PSConstructor n _) -> "  " <> n) constructors)
    , "};"
    ]

generateTemplateParams :: [T.Text] -> T.Text
generateTemplateParams [] = ""
generateTemplateParams vars = 
  "<" <> T.intercalate ", " (map (\v -> "typename " <> v) vars) <> ">"

-- | Generate C++ type alias from PureScript type declaration
generateTypeDecl :: PSTypeDeclaration -> T.Text
generateTypeDecl PSTypeDeclaration{..} =
  "using " <> typeName <> generateTemplateParams typeVars <> " = " <> 
  toCppType typeDefinition <> ";"

-- | Generate C++ function from PureScript value declaration
generateValueDecl :: PSValueDeclaration -> T.Text
generateValueDecl PSValueDeclaration{..} =
  case valueType of
    Just typ -> 
      T.unlines
        [ "inline auto " <> valueName <> "() -> " <> toCppType typ <> " {"
        , "  return " <> generateExpression valueExpression <> ";"
        , "}"
        ]
    Nothing ->
      T.unlines
        [ "inline auto " <> valueName <> "() {"
        , "  return " <> generateExpression valueExpression <> ";"
        , "}"
        ]

-- | Generate C++ concept from PureScript type class
generateClassDecl :: PSClassDeclaration -> T.Text
generateClassDecl PSClassDeclaration{..} =
  T.unlines
    [ "template<typename T>"
    , "concept " <> className <> " = requires(T t) {"
    , T.unlines (map generateConceptRequirement classMembers)
    , "};"
    ]
  where
    generateConceptRequirement PSClassMember{..} =
      "  { t." <> memberName <> "() } -> std::convertible_to<" <> toCppType memberType <> ">;"

-- | Generate C++ template specialization from PureScript instance
generateInstanceDecl :: PSInstanceDeclaration -> T.Text
generateInstanceDecl PSInstanceDeclaration{..} =
  T.unlines
    [ "template<>"
    , "constexpr bool " <> instanceClass <> "<" <> toCppType instanceType <> "> = true;"
    , ""
    , "template<>"
    , "auto " <> instanceClass <> "_impl<" <> toCppType instanceType <> ">() {"
    , T.unlines (map generateInstanceMember instanceMembers)
    , "}"
    ]
  where
    generateInstanceMember PSInstanceMember{..} =
      "  return " <> instanceMemberName <> " = " <> 
      generateExpression instanceMemberExpression <> ";"

generateImplementation :: PSDeclaration -> T.Text
generateImplementation (PSValueDecl decl) = generateValueImpl decl
generateImplementation _ = ""

generateValueImpl :: PSValueDeclaration -> T.Text
generateValueImpl PSValueDeclaration{..} =
  case valueType of
    Just typ ->
      T.unlines
        [ "auto " <> valueName <> "() -> " <> toCppType typ <> " {"
        , "  return " <> generateExpression valueExpression <> ";"
        , "}"
        ]
    Nothing ->
      T.unlines
        [ "auto " <> valueName <> "() {"
        , "  return " <> generateExpression valueExpression <> ";"
        , "}"
        ]

-- | Convert PureScript type to C++ type
toCppType :: PSType -> T.Text
toCppType (PSTypeVar v) = v
toCppType (PSTypeCon "Int" []) = "std::int64_t"
toCppType (PSTypeCon "Number" []) = "double"
toCppType (PSTypeCon "String" []) = "std::string"
toCppType (PSTypeCon "Boolean" []) = "bool"
toCppType (PSTypeCon "Array" [t]) = "std::vector<" <> toCppType t <> ">"
toCppType (PSTypeCon "Maybe" [t]) = "std::optional<" <> toCppType t <> ">"
toCppType (PSTypeCon "Either" [a, b]) = 
  "std::variant<" <> toCppType a <> ", " <> toCppType b <> ">"
toCppType (PSTypeCon "Effect" []) = "std::function<void()>"
toCppType (PSTypeCon "Aff" [t]) = "std::future<" <> toCppType t <> ">"
toCppType (PSTypeCon "Record" [row]) = toCppType row
toCppType (PSTypeCon name args) = 
  name <> "<" <> T.intercalate ", " (map toCppType args) <> ">"
toCppType (PSTypeArr a b) = 
  "std::function<" <> toCppType b <> "(" <> toCppType a <> ")>"
toCppType (PSTypeRecord fields) =
  "struct { " <> T.intercalate "; " (map (\(n, t) -> toCppType t <> " " <> n) fields) <> "; }"
toCppType (PSTypeRow fields) = toCppType (PSTypeRecord fields)
toCppType (PSTypeApp f x) = 
  case f of
    PSTypeCon "Array" [] -> "std::vector<" <> toCppType x <> ">"
    PSTypeCon "Maybe" [] -> "std::optional<" <> toCppType x <> ">"
    PSTypeCon "Either" [] -> "std::variant<" <> toCppType x <> ", std::string>" -- Default to String for error case
    PSTypeCon name [] -> name <> "<" <> toCppType x <> ">"
    _ -> toCppType f <> "<" <> toCppType x <> ">"

-- | Generate C++ expression from PureScript expression
generateExpression :: PSExpression -> T.Text
generateExpression (PSVar v) = v
generateExpression (PSCon c) = c <> "{}"
generateExpression (PSLit (PSLitInt i)) = T.pack (show i)
generateExpression (PSLit (PSLitNumber n)) = T.pack (show n)
generateExpression (PSLit (PSLitString s)) = "\"" <> escapeString s <> "\""
generateExpression (PSLit (PSLitBoolean b)) = if b then "true" else "false"
generateExpression (PSLit (PSLitArray elems)) =
  "std::vector{" <> T.intercalate ", " (map generateExpression elems) <> "}"
generateExpression (PSApp f x) = 
  generateExpression f <> "(" <> generateExpression x <> ")"
generateExpression (PSAbs params body) =
  "[](" <> T.intercalate ", " (map (\p -> "auto " <> p) params) <> ") mutable { " <>
  "return " <> generateExpression body <> "; }"
generateExpression (PSLet bindings body) =
  T.unlines (map (\(n, e) -> "auto " <> n <> " = " <> generateExpression e <> ";") bindings) <>
  "return " <> generateExpression body <> ";"
generateExpression (PSCase expr alts) =
  "std::visit([](auto&& v) -> auto {" <>
  T.unlines (map altToCpp alts) <>
  "  throw std::runtime_error(\"Pattern match failure\");" <>
  "}, " <> generateExpression expr <> ")"
generateExpression (PSIf cond thenExpr elseExpr) =
  "(" <> generateExpression cond <> " ? " <>
  generateExpression thenExpr <> " : " <>
  generateExpression elseExpr <> ")"
generateExpression (PSDo stmts) =
  T.unlines (map generateStatement stmts)
generateExpression (PSRecord fields) =
  "{" <> T.intercalate ", " (map (\(n, e) -> "." <> n <> " = " <> generateExpression e) fields) <> "}"
generateExpression (PSRecordAccess rec field) =
  generateExpression rec <> "." <> field
generateExpression (PSRecordUpdate rec fields) =
  generateExpression rec <> "{" <>
  T.intercalate ", " (map (\(n, e) -> "." <> n <> " = " <> generateExpression e) fields) <>
  "}"

altToCpp :: PSCaseAlternative -> T.Text
altToCpp PSCaseAlternative{..} =
  "  if constexpr (std::is_same_v<std::decay_t<decltype(v)>, " <> 
  patternToCppType casePattern <> ">) {" <>
  "    return " <> generateExpression caseExpression <> ";" <>
  "  }"

patternToCppType :: PSPattern -> T.Text
patternToCppType (PSPatVar v) = "auto"
patternToCppType (PSPatCon c args) = c <> "<" <> T.intercalate ", " (map patternToCppType args) <> ">"
patternToCppType (PSPatLit (PSLitInt i)) = "std::int64_t"
patternToCppType (PSPatLit (PSLitNumber n)) = "double"
patternToCppType (PSPatLit (PSLitString s)) = "std::string"
patternToCppType (PSPatLit (PSLitBoolean b)) = "bool"
patternToCppType PSPatWildcard = "auto"
patternToCppType (PSPatRecord fields) = "struct"

generateStatement :: PSStatement -> T.Text
generateStatement (PSStmtBind pat expr) =
  "auto " <> patternToVar pat <> " = " <> generateExpression expr <> ";"
generateStatement (PSStmtExpr expr) = generateExpression expr <> ";"
generateStatement (PSStmtLet bindings) =
  T.unlines (map (\(n, e) -> "auto " <> n <> " = " <> generateExpression e <> ";") bindings)

patternToVar :: PSPattern -> T.Text
patternToVar (PSPatVar v) = v
patternToVar (PSPatCon c _) = T.toLower c
patternToVar _ = "val"

escapeString :: T.Text -> T.Text
escapeString = T.replace "\"" "\\\"" . T.replace "\n" "\\n" . T.replace "\t" "\\t"
