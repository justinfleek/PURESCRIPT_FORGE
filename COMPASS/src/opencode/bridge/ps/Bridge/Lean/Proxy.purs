-- | Lean LSP Proxy - Lean4 Language Server Protocol Integration
-- |
-- | **What:** Provides a proxy interface to Lean4 Language Server Protocol (LSP)
-- |         via Model Context Protocol (MCP). Enables type checking, goal retrieval,
-- |         tactic application, and theorem searching.
-- | **Why:** Integrates Lean4 proof assistant functionality into Bridge Server,
-- |         allowing clients to interact with Lean4 LSP for proof development.
-- | **How:** Communicates with Lean4 LSP server via MCP, translating between
-- |         JSON-RPC requests and LSP protocol messages.
-- |
-- | **Dependencies:**
-- | - `Bridge.State.Store`: State store for proof state updates
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **LSP Protocol:** Uses Language Server Protocol for communication with Lean4.
-- |   All operations are asynchronous and return Either error or result.
-- | - **Proof State:** Proof state (goals, diagnostics, tactics) is updated in
-- |   state store after each LSP operation.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Lean.Proxy as Lean
-- |
-- | -- Create proxy
-- | proxy <- Lean.createLeanProxy store logger
-- |
-- | -- Check file
-- | diagnostics <- Lean.check proxy "/path/to/File.lean"
-- |
-- | -- Get goals
-- | goals <- Lean.goals proxy "/path/to/File.lean" 10 5
-- | ```
module Bridge.Lean.Proxy where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Pino as Pino

-- | Opaque Lean Proxy type
foreign import data LeanProxy :: Type

-- | Lean goal
type Goal =
  { type_ :: String
  , context :: Array { name :: String, type_ :: String }
  }

-- | Lean diagnostic
type Diagnostic =
  { severity :: Severity
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

data Severity = Error | Warning | Info

derive instance eqSeverity :: Eq Severity

-- | Lean tactic suggestion
type Tactic =
  { tactic :: String
  , confidence :: Number
  }

-- | Create Lean proxy
foreign import createLeanProxyImpl :: StateStore -> Pino.Logger -> Effect LeanProxy

createLeanProxy :: StateStore -> Pino.Logger -> Effect LeanProxy
createLeanProxy = createLeanProxyImpl

-- | Check Lean file
foreign import check :: LeanProxy -> String -> Aff (Either String (Array Diagnostic))

-- | Get goals at position
foreign import goals :: LeanProxy -> String -> Int -> Int -> Aff (Either String (Array Goal))

-- | Get tactic suggestions
foreign import tactics :: LeanProxy -> String -> Int -> Int -> Aff (Either String (Array Tactic))

-- | Apply tactic at position
foreign import applyTactic :: LeanProxy -> String -> Int -> Int -> String -> Maybe Int -> Aff (Either String (Array Goal))

-- | Search theorems
foreign import searchTheorems :: LeanProxy -> String -> Maybe Int -> Maybe String -> Aff (Either String (Array TheoremResult))

-- | Theorem search result
type TheoremResult =
  { name :: String
  , statement :: String
  , file :: String
  , line :: Int
  , description :: Maybe String
  }

-- | Connect to Lean LSP
foreign import connect :: LeanProxy -> Aff (Either String Unit)

-- | Disconnect from Lean LSP
foreign import disconnect :: LeanProxy -> Aff (Either String Unit)
