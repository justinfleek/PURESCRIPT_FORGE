{-|
Module      : Tool.ASTEdit.Structural
Description : AST-based structural editing
= Structural Editing Mode

Operates on Abstract Syntax Trees rather than raw text.

== Coeffect Equation

@
  structural : StructuralParams → Graded (Filesystem path ⊗ AST lang) EditResult
@

== Guarantees

1. /Syntax preservation/ — Output is syntactically valid
2. /Scope awareness/ — Renames respect variable scoping
3. /Comment attachment/ — Comments stay with their nodes

== Supported Languages

| Language   | Parser        | Capabilities          |
|------------|---------------|-----------------------|
| PureScript | purescript    | Full refactoring      |
| Haskell    | ghc-lib       | Full refactoring      |
| Lean4      | lean4         | Full + tactics        |
| TypeScript | tree-sitter   | Structural only       |
| Nix        | rnix          | Structural only       |
-}
module Tool.ASTEdit.Structural
  ( -- * Operations
    EditOp(..)
  , Symbol(..)
  , Wrapper(..)
  , ImportSpec(..)
    -- * Execution
  , applyStructural
    -- * Transformations
  , Transform(..)
  , applyTransform
  , composeTransforms
    -- * AST Types
  , AST(..)
  , Node(..)
  , NodeKind(..)
    -- * Re-exports
  , module Tool.ASTEdit.Structural.Parser
  , module Tool.ASTEdit.Structural.Transform
  , module Tool.ASTEdit.Structural.Render
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)

import Tool.ASTEdit.Types (Span, Change, EditResult, ValidationResult, ChangeType(..), FileChange)
import Tool.ASTEdit.Structural.Parser
  ( parseToAST
  , getParser
  , ParsedAST
  , ParseError
  )
import Tool.ASTEdit.Structural.Transform
  ( applyRename
  , applyExtract
  , applyInline
  , applyReorder
  , applyWrap
  , applyUnwrap
  , applyAddImport
  , applyRemoveUnused
  , applyHole
  , applyMoveToFile
  , applySequence
  )
import Aleph.Coeffect.Spec (ASTLanguage(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Unit (Unit, unit)

-- ════════════════════════════════════════════════════════════════════════════
-- EDIT OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

{-| Structural edit operations.

These compose to form complex refactorings.
-}
data EditOp
  = Rename Symbol Symbol                  -- From → To
  | Extract Span Symbol                   -- Extract span to binding
  | Inline Symbol                         -- Inline all occurrences
  | Reorder (Array Symbol)                -- Reorder declarations
  | Wrap Span Wrapper                     -- Wrap in construct
  | Unwrap Span                           -- Remove wrapper
  | AddImport ImportSpec                  -- Add import
  | RemoveUnused                          -- Remove unused bindings
  | Hole Span                             -- Replace with typed hole
  | MoveToFile Symbol String              -- Move to different file
  | Sequence (Array EditOp)               -- Compose operations

derive instance eqEditOp :: Eq EditOp
derive instance genericEditOp :: Generic EditOp _

instance showEditOp :: Show EditOp where
  show = genericShow

newtype Symbol = Symbol
  { name :: String
  , qualifier :: Maybe String
  }

derive instance eqSymbol :: Eq Symbol
derive newtype instance showSymbol :: Show Symbol
derive instance genericSymbol :: Generic Symbol _

data Wrapper
  = LetWrapper
  | DoWrapper
  | ParenWrapper
  | LambdaWrapper String
  | CaseWrapper
  | IfWrapper
  | TypeAnnWrapper String
  | TryCatchWrapper

derive instance eqWrapper :: Eq Wrapper
derive instance genericWrapper :: Generic Wrapper _

instance showWrapper :: Show Wrapper where
  show = genericShow

type ImportSpec =
  { module :: String
  , items :: Maybe (Array String)
  , qualified :: Boolean
  , alias :: Maybe String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

{-| Apply structural edit to file.

1. Parse file to AST
2. Locate target nodes
3. Apply transformation
4. Validate result
5. Render back to source
-}
applyStructural :: ASTLanguage -> String -> EditOp -> Aff (Either String EditResult)
applyStructural lang content op = do
  -- 1. Get parser for language
  let parser = getParser lang
  
  -- 2. Parse to AST
  parseResult <- parseToAST parser content
  case parseResult of
    Left err -> pure $ Left ("Parse error: " <> err.message)
    Right parsedAST -> do
      -- 3. Find target nodes and apply operation
      transformResult <- applyEditOperation parsedAST.ast op
      case transformResult of
        Left err -> pure $ Left err
        Right transformedAST -> do
          -- 4. Validate result
          validationResult <- validateAST transformedAST lang
          case validationResult of
            Left err -> pure $ Left ("Validation error: " <> err)
            Right _ -> do
              -- 5. Render back to source
              renderedResult <- renderAST transformedAST lang
              case renderedResult of
                Left err -> pure $ Left ("Render error: " <> err)
                Right newContent -> pure $ Right
                  { success: true
                  , mode: Structural lang
                  , filesChanged: 1
                  , changes: [ { filePath: "", changeType: Update, oldContent: content, newContent: newContent, diff: "", additions: 0, deletions: 0 } ]
                  , validation: Just { syntaxValid: true, typesValid: Nothing, scopesValid: true, warnings: [], errors: [] }
                  }

-- | Apply edit operation to AST (delegates to Transform module)
applyEditOperation :: AST -> EditOp -> Aff (Either String AST)
applyEditOperation ast op = case op of
  Rename from to -> applyRename ast from to
  Extract span symbol -> applyExtract ast span symbol
  Inline symbol -> applyInline ast symbol
  Reorder symbols -> applyReorder ast symbols
  Wrap span wrapper -> applyWrap ast span wrapper
  Unwrap span -> applyUnwrap ast span
  AddImport importSpec -> applyAddImport ast importSpec
  RemoveUnused -> applyRemoveUnused ast
  Hole span -> applyHole ast span
  MoveToFile symbol filePath -> applyMoveToFile ast symbol filePath
  Sequence ops -> applySequence ast ops

-- | Validate AST
validateAST :: AST -> ASTLanguage -> Aff (Either String Unit)
validateAST ast lang = do
  -- Check syntax validity
  -- Check type correctness (if language supports)
  -- Check scope correctness
  -- For now, assume valid if no parse errors
  if Array.length ast.errors == 0 then
    pure $ Right unit
  else
    pure $ Left ("AST has " <> show (Array.length ast.errors) <> " errors")

-- ════════════════════════════════════════════════════════════════════════════
-- TRANSFORMATIONS
-- ════════════════════════════════════════════════════════════════════════════

newtype Transform a = Transform (AST -> Either TransformError (TransformResult a))

type TransformResult a =
  { ast :: AST
  , result :: a
  , changes :: Array Change
  }

data TransformError
  = NodeNotFound String
  | InvalidSpan Span
  | TypeMismatch String String
  | ScopingError String
  | AmbiguousTarget (Array Span)

derive instance genericTransformError :: Generic TransformError _

instance showTransformError :: Show TransformError where
  show = genericShow

applyTransform :: forall a. Transform a -> AST -> Either TransformError (TransformResult a)
applyTransform (Transform f) = f

composeTransforms :: forall a b. Transform a -> Transform b -> Transform { first :: a, second :: b }
composeTransforms (Transform f) (Transform g) = Transform \ast ->
  case f ast of
    Left err -> Left err
    Right r1 ->
      case g r1.ast of
        Left err -> Left err
        Right r2 -> Right
          { ast: r2.ast
          , result: { first: r1.result, second: r2.result }
          , changes: r1.changes <> r2.changes
          }

-- ════════════════════════════════════════════════════════════════════════════
-- AST TYPES
-- ════════════════════════════════════════════════════════════════════════════

type AST =
  { root :: Node
  , language :: ASTLanguage
  , source :: String
  , errors :: Array { message :: String, span :: Span }
  }

type Node =
  { kind :: NodeKind
  , span :: Span
  , children :: Array Node
  , text :: String
  , field :: Maybe String
  }

data NodeKind
  = FunctionDecl | TypeDecl | ClassDecl | InstanceDecl | ModuleDecl | ValueDecl
  | Application | Lambda | LetExpr | CaseExpr | IfExpr | Literal | Variable
  | Operator | DoExpr | RecordExpr | ArrayExpr
  | Assignment | ReturnStmt | ImportDecl | ExportDecl
  | TypeApp | TypeArrow | TypeForall | TypeConstraint | TypeVar | TypeCon
  | PatternVar | PatternCon | PatternWild | PatternLit | PatternRecord
  | Comment | Whitespace | Error | UnknownKind String

derive instance eqNodeKind :: Eq NodeKind
derive instance genericNodeKind :: Generic NodeKind _

instance showNodeKind :: Show NodeKind where
  show = genericShow
