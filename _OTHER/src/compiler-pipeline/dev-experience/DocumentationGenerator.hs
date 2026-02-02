{-# LANGUAGE OverloadedStrings #-}
-- Phase 7: Documentation Generation
module DocumentationGenerator where

import qualified Data.Text as T
import Parser (PSModule(..), PSDeclaration(..), PSValueDeclaration(..), 
               PSDataDeclaration(..), PSConstructor(..), PSTypeDeclaration(..),
               PSClassDeclaration(..), PSClassMember(..), PSExpression(..), 
               PSLiteral(..), PSCaseAlternative(..), PSPattern(..), PSStatement(..),
               PSType(..))

-- | Generate documentation from module
generateDocumentation :: PSModule -> T.Text
generateDocumentation module'@PSModule{..} =
  let moduleDoc = generateModuleDoc module'
      declarationsDoc = T.unlines $ map generateDeclarationDoc moduleDeclarations
  in moduleDoc <> "\n" <> declarationsDoc

-- | Generate module documentation
generateModuleDoc :: PSModule -> T.Text
generateModuleDoc module' =
  "# Module: " <> moduleName module' <> "\n\n" <>
  "## Overview\n\n" <>
  "This module contains " <> T.pack (show (length (moduleDeclarations module'))) <> " declarations.\n\n"

-- | Generate declaration documentation
generateDeclarationDoc :: PSDeclaration -> T.Text
generateDeclarationDoc (PSValueDecl decl) =
  "## " <> valueName decl <> "\n\n" <>
  case valueType decl of
    Just typ -> "**Type**: " <> formatType typ <> "\n\n"
    Nothing -> ""
  "**Definition**:\n```purescript\n" <>
  formatValueDecl decl <>
  "\n```\n\n"
generateDeclarationDoc (PSDataDecl decl) =
  "## " <> dataName decl <> "\n\n" <>
  "**Data Declaration**:\n```purescript\n" <>
  formatDataDecl decl <>
  "\n```\n\n"
generateDeclarationDoc (PSTypeDecl decl) =
  "## " <> typeName decl <> "\n\n" <>
  "**Type Declaration**:\n```purescript\n" <>
  formatTypeDecl decl <>
  "\n```\n\n"
generateDeclarationDoc (PSClassDecl decl) =
  "## " <> className decl <> "\n\n" <>
  "**Type Class**:\n```purescript\n" <>
  formatClassDecl decl <>
  "\n```\n\n"
generateDeclarationDoc (PSInstanceDecl _) = ""

-- | Format type
formatType :: PSType -> T.Text
formatType (PSTypeArr from to) = formatType from <> " -> " <> formatType to
formatType (PSTypeCon name []) = name
formatType (PSTypeCon name args) =
  name <> " " <> T.unwords (map formatType args)
formatType (PSTypeVar name) = name
formatType (PSTypeApp f x) = formatType f <> " " <> formatType x
formatType (PSTypeRecord fields) =
  "{ " <> T.intercalate ", " (map (\(n, t) -> n <> " :: " <> formatType t) fields) <> " }"
formatType (PSTypeRow fields) =
  "(" <> T.intercalate ", " (map (\(n, t) -> n <> " :: " <> formatType t) fields) <> ")"

-- | Format value declaration
formatValueDecl :: PSValueDeclaration -> T.Text
formatValueDecl decl =
  case valueType decl of
    Just typ -> valueName decl <> " :: " <> formatType typ <> "\n"
    Nothing -> ""
  valueName decl <> " = " <> formatExpression (valueExpression decl)

-- | Format data declaration
formatDataDecl :: PSDataDeclaration -> T.Text
formatDataDecl decl =
  "data " <> dataName decl <> " " <> T.unwords (dataTypeVars decl) <> " = " <>
  T.intercalate " | " (map formatConstructor (dataConstructors decl))

-- | Format constructor
formatConstructor :: PSConstructor -> T.Text
formatConstructor (PSConstructor name args) =
  name <> " " <> T.unwords (map formatType args)

-- | Format type declaration
formatTypeDecl :: PSTypeDeclaration -> T.Text
formatTypeDecl decl =
  "type " <> typeName decl <> " " <> T.unwords (typeVars decl) <> " = " <>
  formatType (typeDefinition decl)

-- | Format class declaration
formatClassDecl :: PSClassDeclaration -> T.Text
formatClassDecl decl =
  "class " <> className decl <> " " <> T.unwords (classVars decl) <> " where\n" <>
  T.unlines (map formatClassMember (classMembers decl))

-- | Format class member
formatClassMember :: PSClassMember -> T.Text
formatClassMember (PSClassMember name typ) =
  "  " <> name <> " :: " <> formatType typ

-- | Format expression (simplified)
formatExpression :: PSExpression -> T.Text
formatExpression (PSVar name) = name
formatExpression (PSLit lit) = formatLiteral lit
formatExpression (PSApp f x) = formatExpression f <> " " <> formatExpression x
formatExpression (PSAbs params body) =
  "\\" <> T.unwords params <> " -> " <> formatExpression body
formatExpression (PSLet bindings body) =
  "let " <> T.intercalate "; " (map (\(n, e) -> n <> " = " <> formatExpression e) bindings) <>
  " in " <> formatExpression body
formatExpression (PSCase expr alts) =
  "case " <> formatExpression expr <> " of\n" <>
  T.unlines (map formatCaseAlt alts)
formatExpression (PSIf cond thenExpr elseExpr) =
  "if " <> formatExpression cond <> " then " <> formatExpression thenExpr <>
  " else " <> formatExpression elseExpr
formatExpression (PSDo stmts) =
  "do\n" <> T.unlines (map formatStatement stmts)
formatExpression (PSRecord fields) =
  "{ " <> T.intercalate ", " (map (\(n, e) -> n <> " = " <> formatExpression e) fields) <> " }"
formatExpression (PSRecordAccess expr field) =
  formatExpression expr <> "." <> field
formatExpression (PSRecordUpdate expr fields) =
  formatExpression expr <> " { " <> T.intercalate ", " (map (\(n, e) -> n <> " = " <> formatExpression e) fields) <> " }"

-- | Format case alternative
formatCaseAlt :: PSCaseAlternative -> T.Text
formatCaseAlt alt =
  formatPattern (casePattern alt) <> " -> " <> formatExpression (caseExpression alt)

-- | Format pattern
formatPattern :: PSPattern -> T.Text
formatPattern (PSPatVar name) = name
formatPattern (PSPatCon name args) = name <> " " <> T.unwords (map formatPattern args)
formatPattern (PSPatLit lit) = formatLiteral lit
formatPattern PSPatWildcard = "_"
formatPattern (PSPatRecord fields) =
  "{ " <> T.intercalate ", " (map (\(n, p) -> n <> " = " <> formatPattern p) fields) <> " }"

-- | Format statement
formatStatement :: PSStatement -> T.Text
formatStatement (PSStmtBind pat expr) = formatPattern pat <> " <- " <> formatExpression expr
formatStatement (PSStmtExpr expr) = formatExpression expr
formatStatement (PSStmtLet bindings) =
  "let " <> T.intercalate "; " (map (\(n, e) -> n <> " = " <> formatExpression e) bindings)

-- | Format literal
formatLiteral :: PSLiteral -> T.Text
formatLiteral (PSLitInt i) = T.pack (show i)
formatLiteral (PSLitNumber n) = T.pack (show n)
formatLiteral (PSLitString s) = "\"" <> s <> "\""
formatLiteral (PSLitBoolean b) = if b then "true" else "false"
formatLiteral (PSLitArray elems) = "[" <> T.intercalate ", " (map formatExpression elems) <> "]"
