-- | PTY (Pseudo Terminal)
-- |
-- | Creates and manages PTY sessions for terminal emulation.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/pty/index.ts
module Forge.PTY.Index
  ( Info
  , CreateInput
  , UpdateInput
  , event
  , list
  , get
  , create
  , update
  , remove
  , resize
  , write
  , connect
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)
import Data.Maybe (Maybe)

-- | PTY session info
type Info =
  { id :: String
  , title :: String
  , command :: String
  , args :: Array String
  , cwd :: String
  , status :: String  -- "running" | "exited"
  , pid :: Int
  }

-- | Input for creating PTY
type CreateInput =
  { command :: Maybe String
  , args :: Maybe (Array String)
  , cwd :: Maybe String
  , title :: Maybe String
  , env :: Maybe Foreign
  }

-- | Input for updating PTY
type UpdateInput =
  { title :: Maybe String
  , size :: Maybe { rows :: Int, cols :: Int }
  }

-- | PTY events
foreign import event :: Foreign

-- | List all PTY sessions
foreign import list :: Array Info

-- | Get PTY session by ID
foreign import get :: String -> Maybe Info

-- | Create new PTY session
foreign import create :: CreateInput -> Aff Info

-- | Update PTY session
foreign import update :: String -> UpdateInput -> Aff (Maybe Info)

-- | Remove PTY session
foreign import remove :: String -> Aff Unit

-- | Resize PTY
foreign import resize :: String -> Int -> Int -> Unit

-- | Write to PTY
foreign import write :: String -> String -> Unit

-- | Connect WebSocket to PTY
foreign import connect :: String -> Foreign -> Foreign
