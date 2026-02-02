module Nexus.AgentSocial.FFI where

import Prelude

-- | Generate deterministic ID from namespace and seed
-- | Same namespace + seed always produces same ID
foreign import generateIdFromSeed :: String -> Int -> String

-- | Format timestamp (milliseconds since epoch) as ISO 8601 string
-- | Deterministic: same input always produces same output
foreign import formatTimestamp :: Number -> String

-- | Generate deterministic avatar URL from agent ID and display name
-- | Creates SVG avatar with colored background and initials
-- | Deterministic: same agentId + displayName always produces same avatar
foreign import generateAvatarUrl :: String -> String -> Effect String

-- | Generate avatar URL from semantic cell state
-- | Uses cell position (first 3 dims) for color, energy for brightness, grade for opacity, spin for rotation
-- | Falls back to generateAvatarUrl if cell state is unavailable or invalid
-- | Parameters: agentId -> displayName -> cellStateJson -> Effect String
foreign import generateAvatarFromCellState :: String -> String -> String -> Effect String
