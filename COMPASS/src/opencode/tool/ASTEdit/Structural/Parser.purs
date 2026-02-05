{-|
Module      : Tool.ASTEdit.Structural.Parser
Description : Language parser FFI for AST editing
= Parser Interface

Foreign function interface for parsing source code to ASTs.
Supports multiple languages via different parser backends.
-}
module Tool.ASTEdit.Structural.Parser
  ( -- * Parser Interface
    parseToAST
  , parseError
    -- * Language Support
  , LanguageParser(..)
  , getParser
    -- * AST Types
  , ParsedAST(..)
  , ParseError(..)
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Tool.ASTEdit.Structural (AST, Node, NodeKind)
import Aleph.Coeffect.Spec (ASTLanguage(..))

-- ============================================================================
-- PARSER TYPES
-- ============================================================================

{-| Parser for a specific language.
-}
data LanguageParser
  = TreeSitterParser String  -- Language name (typescript, nix, etc.)
  | PureScriptParser
  | HaskellParser
  | Lean4Parser

derive instance eqLanguageParser :: Eq LanguageParser
derive instance genericLanguageParser :: Generic LanguageParser _

instance showLanguageParser :: Show LanguageParser where
  show = genericShow

{-| Parsed AST result.
-}
type ParsedAST =
  { ast :: AST
  , language :: ASTLanguage
  , source :: String
  , errors :: Array ParseError
  }

{-| Parse error with location.
-}
type ParseError =
  { message :: String
  , line :: Int
  , column :: Int
  , span :: { start :: Int, end :: Int }
  }

-- ============================================================================
-- PARSER SELECTION
-- ============================================================================

{-| Get parser for language.
-}
getParser :: ASTLanguage -> LanguageParser
getParser = case _ of
  ASTPureScript -> PureScriptParser
  ASTHaskell -> HaskellParser
  ASTLean4 -> Lean4Parser
  ASTTypeScript -> TreeSitterParser "typescript"
  ASTNix -> TreeSitterParser "nix"
  ASTPython -> TreeSitterParser "python"
  ASTRust -> TreeSitterParser "rust"
  ASTUnknown _ -> TreeSitterParser "typescript"  -- Default fallback

-- ============================================================================
-- PARSER INTERFACE
-- ============================================================================

{-| Parse source code to AST.

@
  parseToAST : LanguageParser -> String -> Aff (Either ParseError ParsedAST)
@
-}
foreign import parseToAST :: LanguageParser -> String -> Aff (Either ParseError ParsedAST)

{-| Parse error message from exception.
-}
foreign import parseError :: String -> ParseError
