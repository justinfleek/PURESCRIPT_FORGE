-- | Agent color utilities
-- | Migrated from: forge-dev/packages/app/src/utils/agent.ts (12 lines)
module Sidepanel.Utils.Agent
  ( agentColor
  , defaultAgentColors
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Tuple (Tuple(..))

-- | Default agent color CSS variables
defaultAgentColors :: Map String String
defaultAgentColors = Map.fromFoldable
  [ Tuple "ask" "var(--icon-agent-ask-base)"
  , Tuple "build" "var(--icon-agent-build-base)"
  , Tuple "docs" "var(--icon-agent-docs-base)"
  , Tuple "plan" "var(--icon-agent-plan-base)"
  ]

-- | Get the color for an agent
-- | Returns custom color if provided, otherwise looks up default
-- | Falls back to lowercase name lookup
agentColor :: String -> Maybe String -> Maybe String
agentColor name custom = case custom of
  Just c -> Just c
  Nothing -> 
    let lowercase = String.toLower name
    in Map.lookup name defaultAgentColors
         <|> Map.lookup lowercase defaultAgentColors

-- | Alternative operator for Maybe
infixl 3 alt as <|>

alt :: forall a. Maybe a -> Maybe a -> Maybe a
alt (Just x) _ = Just x
alt Nothing y = y
