{-|
Module      : Tool.ASTEdit.Structural
Description : AST-based structural editing
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

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
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)

import Tool.ASTEdit.Types (Span, Change, EditResult, ValidationResult)
import Aleph.Coeffect.Spec (ASTLanguage(..))

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
  -- TODO: Implementation
  -- 1. Get parser for language
  -- 2. Parse to AST
  -- 3. Find target nodes
  -- 4. Apply operation
  -- 5. Validate
  -- 6. Render
  pure $ Left "Structural editing not yet implemented"

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
