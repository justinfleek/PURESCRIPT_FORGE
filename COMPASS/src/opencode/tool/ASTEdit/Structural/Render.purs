{-|
Module      : Tool.ASTEdit.Structural.Render
Description : AST rendering to source code
= AST Rendering

Renders ASTs back to source code, preserving formatting where possible.
-}
module Tool.ASTEdit.Structural.Render
  ( -- * Rendering
    renderAST
  , renderNode
    -- * Formatting
    preserveFormatting
    -- * Helpers
  , getChildText
  , getChildByKind
  , getChildrenByKind
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.String as String
import Effect.Aff (Aff)
import Tool.ASTEdit.Structural (AST, Node, NodeKind(..))
import Tool.ASTEdit.Types (Span)
import Aleph.Coeffect.Spec (ASTLanguage(..))
import Data.Ord (compare)

-- ============================================================================
-- RENDERING
-- ============================================================================

{-| Render AST to source code.

Attempts to preserve original formatting when possible.
-}
renderAST :: AST -> ASTLanguage -> Aff (Either String String)
renderAST ast lang = do
  -- If AST has source, use formatting preservation
  let rendered = if String.length ast.source > 0 then
        preserveFormatting ast ast.source
      else
        renderNode ast.root lang
  pure $ Right rendered

-- | Render node to source code
renderNode :: Node -> ASTLanguage -> String
renderNode node lang = case node.kind of
  FunctionDecl -> renderFunctionDecl node lang
  TypeDecl -> renderTypeDecl node lang
  ClassDecl -> renderClassDecl node lang
  InstanceDecl -> renderInstanceDecl node lang
  ModuleDecl -> renderModuleDecl node lang
  ValueDecl -> renderValueDecl node lang
  ImportDecl -> renderImportDecl node lang
  ExportDecl -> renderExportDecl node lang
  Application -> renderApplication node lang
  Lambda -> renderLambda node lang
  LetExpr -> renderLetExpr node lang
  CaseExpr -> renderCaseExpr node lang
  IfExpr -> renderIfExpr node lang
  Literal -> renderLiteral node lang
  Variable -> renderVariable node lang
  Operator -> renderOperator node lang
  DoExpr -> renderDoExpr node lang
  RecordExpr -> renderRecordExpr node lang
  ArrayExpr -> renderArrayExpr node lang
  Assignment -> renderAssignment node lang
  ReturnStmt -> renderReturnStmt node lang
  TypeApp -> renderTypeApp node lang
  TypeArrow -> renderTypeArrow node lang
  TypeForall -> renderTypeForall node lang
  TypeConstraint -> renderTypeConstraint node lang
  TypeVar -> renderTypeVar node lang
  TypeCon -> renderTypeCon node lang
  PatternVar -> renderPatternVar node lang
  PatternCon -> renderPatternCon node lang
  PatternWild -> renderPatternWild node lang
  PatternLit -> renderPatternLit node lang
  PatternRecord -> renderPatternRecord node lang
  Comment -> node.text
  Whitespace -> node.text
  Error -> node.text
  UnknownKind _ -> node.text

-- ============================================================================
-- LANGUAGE-SPECIFIC RENDERING
-- ============================================================================

-- | Render function declaration
renderFunctionDecl :: Node -> ASTLanguage -> String
renderFunctionDecl node lang = case lang of
  ASTPureScript -> renderPureScriptFunction node
  ASTHaskell -> renderHaskellFunction node
  ASTTypeScript -> renderTypeScriptFunction node
  _ -> node.text  -- Fallback to original text

renderPureScriptFunction :: Node -> String
renderPureScriptFunction node = do
  let name = getChildText "name" node
  let params = getChildrenByKind PatternVar node
  let body = getChildByKind Application node <|> getChildByKind Lambda node
  let typeSig = getChildByKind TypeArrow node
  case typeSig of
    Just sig -> name <> " :: " <> renderNode sig ASTPureScript <> "\n" <> name <> " " <> String.joinWith " " (map (\p -> renderNode p ASTPureScript) params) <> " = " <> (case body of Just b -> renderNode b ASTPureScript; Nothing -> "")
    Nothing -> name <> " " <> String.joinWith " " (map (\p -> renderNode p ASTPureScript) params) <> " = " <> (case body of Just b -> renderNode b ASTPureScript; Nothing -> "")

renderHaskellFunction :: Node -> String
renderHaskellFunction node = renderPureScriptFunction node  -- Similar syntax

renderTypeScriptFunction :: Node -> String
renderTypeScriptFunction node = do
  let name = getChildText "name" node
  let params = getChildrenByKind PatternVar node
  let body = getChildByKind Application node
  "function " <> name <> "(" <> String.joinWith ", " (map (\p -> renderNode p ASTTypeScript) params) <> ") {" <> (case body of Just b -> renderNode b ASTTypeScript; Nothing -> "") <> "}"

-- | Render type declaration
renderTypeDecl :: Node -> ASTLanguage -> String
renderTypeDecl node lang = case lang of
  ASTPureScript -> "type " <> getChildText "name" node <> " = " <> String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)
  ASTHaskell -> "type " <> getChildText "name" node <> " = " <> String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)
  ASTTypeScript -> "type " <> getChildText "name" node <> " = " <> String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)
  _ -> node.text

-- | Render class declaration
renderClassDecl :: Node -> ASTLanguage -> String
renderClassDecl node lang = case lang of
  ASTPureScript -> "class " <> getChildText "name" node <> " where\n  " <> String.joinWith "\n  " (map (\c -> renderNode c lang) node.children)
  ASTHaskell -> renderClassDecl node ASTPureScript
  _ -> node.text

-- | Render instance declaration
renderInstanceDecl :: Node -> ASTLanguage -> String
renderInstanceDecl node lang = case lang of
  ASTPureScript -> "instance " <> getChildText "class" node <> " " <> getChildText "type" node <> " where\n  " <> String.joinWith "\n  " (map (\c -> renderNode c lang) node.children)
  ASTHaskell -> renderInstanceDecl node ASTPureScript
  _ -> node.text

-- | Render module declaration
renderModuleDecl :: Node -> ASTLanguage -> String
renderModuleDecl node lang = case lang of
  ASTPureScript -> "module " <> getChildText "name" node <> " where"
  ASTHaskell -> "module " <> getChildText "name" node <> " where"
  _ -> node.text

-- | Render value declaration
renderValueDecl :: Node -> ASTLanguage -> String
renderValueDecl node lang = node.text  -- Preserve original

-- | Render import declaration
renderImportDecl :: Node -> ASTLanguage -> String
renderImportDecl node lang = case lang of
  ASTPureScript -> "import " <> getChildText "module" node
  ASTHaskell -> "import " <> getChildText "module" node
  ASTTypeScript -> "import " <> getChildText "module" node
  _ -> node.text

-- | Render export declaration
renderExportDecl :: Node -> ASTLanguage -> String
renderExportDecl node lang = case lang of
  ASTPureScript -> "module " <> getChildText "module" node <> " (" <> String.joinWith ", " (Array.map (\c -> renderNode c lang) node.children) <> ")"
  _ -> node.text

-- | Render application
renderApplication :: Node -> ASTLanguage -> String
renderApplication node lang = String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)

-- | Render lambda
renderLambda :: Node -> ASTLanguage -> String
renderLambda node lang = case lang of
  ASTPureScript -> "\\" <> String.joinWith " " (map (\c -> renderNode c lang) (Array.take 1 node.children)) <> " -> " <> String.joinWith " " (map (\c -> renderNode c lang) (Array.drop 1 node.children))
  ASTHaskell -> renderLambda node ASTPureScript
  ASTTypeScript -> "(" <> String.joinWith ", " (map (\c -> renderNode c lang) (Array.take 1 node.children)) <> ") => " <> String.joinWith " " (map (\c -> renderNode c lang) (Array.drop 1 node.children))
  _ -> node.text

-- | Render let expression
renderLetExpr :: Node -> ASTLanguage -> String
renderLetExpr node lang = case lang of
  ASTPureScript -> "let " <> String.joinWith "\n    " (map (\c -> renderNode c lang) (Array.take (Array.length node.children - 1) node.children)) <> "\n  in " <> (case Array.last node.children of Just last -> renderNode last lang; Nothing -> "")
  ASTHaskell -> renderLetExpr node ASTPureScript
  _ -> node.text

-- | Render case expression
renderCaseExpr :: Node -> ASTLanguage -> String
renderCaseExpr node lang = case lang of
  ASTPureScript -> "case " <> (case Array.head node.children of Just h -> renderNode h lang; Nothing -> "") <> " of\n  " <> String.joinWith "\n  " (map (\c -> renderNode c lang) (Array.drop 1 node.children))
  ASTHaskell -> renderCaseExpr node ASTPureScript
  _ -> node.text

-- | Render if expression
renderIfExpr :: Node -> ASTLanguage -> String
renderIfExpr node lang = case lang of
  ASTPureScript -> "if " <> (case Array.head node.children of Just cond -> renderNode cond lang; Nothing -> "") <> " then " <> (case Array.index node.children 1 of Just then_ -> renderNode then_ lang; Nothing -> "") <> " else " <> (case Array.index node.children 2 of Just else_ -> renderNode else_ lang; Nothing -> "")
  ASTHaskell -> renderIfExpr node ASTPureScript
  ASTTypeScript -> "if (" <> (case Array.head node.children of Just cond -> renderNode cond lang; Nothing -> "") <> ") { " <> (case Array.index node.children 1 of Just then_ -> renderNode then_ lang; Nothing -> "") <> " } else { " <> (case Array.index node.children 2 of Just else_ -> renderNode else_ lang; Nothing -> "") <> " }"
  _ -> node.text

-- | Render literal
renderLiteral :: Node -> ASTLanguage -> String
renderLiteral node lang = node.text

-- | Render variable
renderVariable :: Node -> ASTLanguage -> String
renderVariable node lang = node.text

-- | Render operator
renderOperator :: Node -> ASTLanguage -> String
renderOperator node lang = node.text

-- | Render do expression
renderDoExpr :: Node -> ASTLanguage -> String
renderDoExpr node lang = case lang of
  ASTPureScript -> "do\n  " <> String.joinWith "\n  " (Array.map (\c -> renderNode c lang) node.children)
  ASTHaskell -> renderDoExpr node ASTPureScript
  _ -> node.text

-- | Render record expression
renderRecordExpr :: Node -> ASTLanguage -> String
renderRecordExpr node lang = "{" <> String.joinWith ", " (Array.map (\c -> renderNode c lang) node.children) <> "}"

-- | Render array expression
renderArrayExpr :: Node -> ASTLanguage -> String
renderArrayExpr node lang = "[" <> String.joinWith ", " (Array.map (\c -> renderNode c lang) node.children) <> "]"

-- | Render assignment
renderAssignment :: Node -> ASTLanguage -> String
renderAssignment node lang = (case Array.head node.children of Just lhs -> renderNode lhs lang; Nothing -> "") <> " = " <> (case Array.index node.children 1 of Just rhs -> renderNode rhs lang; Nothing -> "")

-- | Render return statement
renderReturnStmt :: Node -> ASTLanguage -> String
renderReturnStmt node lang = case lang of
  ASTTypeScript -> "return " <> String.joinWith " " (Array.map (\c -> renderNode c lang) node.children) <> ";"
  _ -> node.text

-- | Render type application
renderTypeApp :: Node -> ASTLanguage -> String
renderTypeApp node lang = String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)

-- | Render type arrow
renderTypeArrow :: Node -> ASTLanguage -> String
renderTypeArrow node lang = String.joinWith " -> " (Array.map (\c -> renderNode c lang) node.children)

-- | Render type forall
renderTypeForall :: Node -> ASTLanguage -> String
renderTypeForall node lang = "forall " <> String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)

-- | Render type constraint
renderTypeConstraint :: Node -> ASTLanguage -> String
renderTypeConstraint node lang = String.joinWith " " (Array.map (\c -> renderNode c lang) node.children)

-- | Render type variable
renderTypeVar :: Node -> ASTLanguage -> String
renderTypeVar node lang = node.text

-- | Render type constructor
renderTypeCon :: Node -> ASTLanguage -> String
renderTypeCon node lang = node.text

-- | Render pattern variable
renderPatternVar :: Node -> ASTLanguage -> String
renderPatternVar node lang = node.text

-- | Render pattern constructor
renderPatternCon :: Node -> ASTLanguage -> String
renderPatternCon node lang = node.text

-- | Render pattern wildcard
renderPatternWild :: Node -> ASTLanguage -> String
renderPatternWild node lang = "_"

-- | Render pattern literal
renderPatternLit :: Node -> ASTLanguage -> String
renderPatternLit node lang = node.text

-- | Render pattern record
renderPatternRecord :: Node -> ASTLanguage -> String
renderPatternRecord node lang = "{" <> String.joinWith ", " (map (\c -> renderNode c lang) node.children) <> "}"

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Get child text by field name
getChildText :: String -> Node -> String
getChildText fieldName node = case Array.find (\c -> c.field == Just fieldName) node.children of
  Just child -> child.text
  Nothing -> ""

-- | Get child by kind
getChildByKind :: NodeKind -> Node -> Maybe Node
getChildByKind kind node = Array.find (\c -> c.kind == kind) node.children

-- | Get children by kind
getChildrenByKind :: NodeKind -> Node -> Array Node
getChildrenByKind kind node = Array.filter (\c -> c.kind == kind) node.children

-- | Preserve formatting from original source
preserveFormatting :: AST -> String -> String
preserveFormatting ast original = 
  -- Strategy: Render AST nodes, but preserve original formatting for unmodified regions
  -- 1. Collect all modified spans from AST (nodes that were transformed)
  -- 2. For modified spans: use rendered AST
  -- 3. For unmodified spans: use original source
  -- 4. Preserve whitespace and comments between nodes
  
  let modifiedSpans = collectModifiedSpans ast.root []
      -- Sort spans by start byte (ascending)
      sortedSpans = Array.sortBy (\s1 s2 -> compare s1.startByte s2.startByte) modifiedSpans
      -- Build result by interleaving original and rendered content
      result = buildFormattedOutput ast original sortedSpans 0
  in result

-- | Collect all spans that were modified (have rendered content different from original)
collectModifiedSpans :: Node -> Array Span -> Array Span
collectModifiedSpans node acc =
  -- For now, mark all nodes as potentially modified
  -- In a full implementation, would track which nodes were actually transformed
  let currentAcc = if shouldPreserveNode node then acc else node.span : acc
      childrenAcc = Array.foldl (\acc' child -> collectModifiedSpans child acc') currentAcc node.children
  in childrenAcc

-- | Check if node should preserve original formatting (comments, whitespace)
shouldPreserveNode :: Node -> Boolean
shouldPreserveNode node = case node.kind of
  Comment -> true
  Whitespace -> true
  _ -> false

-- | Build formatted output by interleaving original and rendered content
buildFormattedOutput :: AST -> String -> Array Span -> Int -> String
buildFormattedOutput ast original modifiedSpans currentPos =
  case Array.head modifiedSpans of
    Nothing -> 
      -- No more modified spans, append rest of original
      String.drop currentPos original
    Just span ->
      if span.startByte < currentPos then
        -- Skip overlapping spans (shouldn't happen if sorted correctly)
        buildFormattedOutput ast original (Array.drop 1 modifiedSpans) currentPos
      else
        -- Append original content before modified span
        let beforeModified = String.take (span.startByte - currentPos) (String.drop currentPos original)
            -- Render the modified node
            modifiedContent = renderNodeSpan ast span
            -- Continue with remaining spans
            rest = buildFormattedOutput ast original (Array.drop 1 modifiedSpans) span.endByte
        in beforeModified <> modifiedContent <> rest

-- | Render a specific node span from AST
renderNodeSpan :: AST -> Span -> String
renderNodeSpan ast span =
  -- Find node at span and render it
  case findNodeAtSpan ast.root span of
    Nothing -> 
      -- Fallback: use original text from span
      String.take (span.endByte - span.startByte) (String.drop span.startByte ast.source)
    Just node ->
      -- Render node using language-specific renderer
      renderNode node ast.language

-- | Find node at specific span
findNodeAtSpan :: Node -> Span -> Maybe Node
findNodeAtSpan node span =
  if spanMatchesFormatting node.span span then
    Just node
  else
    Array.findMap (\child -> findNodeAtSpan child span) node.children

-- | Check if spans match (within tolerance for formatting)
-- Uses overlap-based matching for formatting preservation
spanMatchesFormatting :: Span -> Span -> Boolean
spanMatchesFormatting s1 s2 =
  -- Match if spans overlap significantly (allows for minor formatting differences)
  s1.startByte <= s2.endByte && s1.endByte >= s2.startByte
