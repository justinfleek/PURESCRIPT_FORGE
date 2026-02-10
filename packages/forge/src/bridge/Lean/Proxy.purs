-- | Lean LSP Proxy - Lean4 Language Server Protocol Integration
-- | Communicates with Lean4 LSP server via MCP
module Bridge.Lean.Proxy where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
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

-- | Lean diagnostic severity
data Severity = Error | Warning | Info

derive instance eqSeverity :: Eq Severity

instance showSeverity :: Show Severity where
  show Error = "error"
  show Warning = "warning"
  show Info = "info"

-- | Lean diagnostic
type Diagnostic =
  { severity :: Severity
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

-- | Lean tactic suggestion
type Tactic =
  { tactic :: String
  , confidence :: Number
  }

-- | Theorem search result
type TheoremResult =
  { name :: String
  , statement :: String
  , file :: String
  , line :: Int
  , description :: Maybe String
  }

-- | FFI declarations (top-level)
foreign import createLeanProxyImpl :: StateStore -> Pino.Logger -> Effect LeanProxy
foreign import checkImpl :: LeanProxy -> String -> EffectFnAff (Either String (Array Diagnostic))
foreign import goalsImpl :: LeanProxy -> String -> Int -> Int -> EffectFnAff (Either String (Array Goal))
foreign import tacticsImpl :: LeanProxy -> String -> Int -> Int -> EffectFnAff (Either String (Array Tactic))
foreign import applyTacticImpl :: LeanProxy -> String -> Int -> Int -> String -> Maybe Int -> EffectFnAff (Either String (Array Goal))
foreign import searchTheoremsImpl :: LeanProxy -> String -> Maybe Int -> Maybe String -> EffectFnAff (Either String (Array TheoremResult))
foreign import connectImpl :: LeanProxy -> EffectFnAff (Either String Unit)
foreign import disconnectImpl :: LeanProxy -> EffectFnAff (Either String Unit)

-- | Create Lean proxy
createLeanProxy :: StateStore -> Pino.Logger -> Effect LeanProxy
createLeanProxy = createLeanProxyImpl

-- | Check Lean file
check :: LeanProxy -> String -> Aff (Either String (Array Diagnostic))
check proxy file = fromEffectFnAff $ checkImpl proxy file

-- | Get goals at position
goals :: LeanProxy -> String -> Int -> Int -> Aff (Either String (Array Goal))
goals proxy file line col = fromEffectFnAff $ goalsImpl proxy file line col

-- | Get tactic suggestions
tactics :: LeanProxy -> String -> Int -> Int -> Aff (Either String (Array Tactic))
tactics proxy file line col = fromEffectFnAff $ tacticsImpl proxy file line col

-- | Apply tactic at position
applyTactic :: LeanProxy -> String -> Int -> Int -> String -> Maybe Int -> Aff (Either String (Array Goal))
applyTactic proxy file line col tactic goalIdx =
  fromEffectFnAff $ applyTacticImpl proxy file line col tactic goalIdx

-- | Search theorems
searchTheorems :: LeanProxy -> String -> Maybe Int -> Maybe String -> Aff (Either String (Array TheoremResult))
searchTheorems proxy query limit file =
  fromEffectFnAff $ searchTheoremsImpl proxy query limit file

-- | Connect to Lean LSP
connect :: LeanProxy -> Aff (Either String Unit)
connect proxy = fromEffectFnAff $ connectImpl proxy

-- | Disconnect from Lean LSP
disconnect :: LeanProxy -> Aff (Either String Unit)
disconnect proxy = fromEffectFnAff $ disconnectImpl proxy
