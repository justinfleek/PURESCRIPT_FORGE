-- | SerializeAddon - Serialize terminal buffer contents
-- |
-- | Migrated from: forge-dev/packages/app/src/addons/serialize.ts (592 lines)
-- |
-- | Port of xterm.js addon-serialize for ghostty-web.
-- | Enables serialization of terminal contents to a string that can
-- | be written back to restore terminal state.
-- |
-- | Usage:
-- | ```purescript
-- | serializeAddon <- SerializeAddon.new
-- | Terminal.loadAddon term serializeAddon
-- | content <- SerializeAddon.serialize serializeAddon Nothing
-- | ```
module App.Addons.Serialize
  ( SerializeAddon
  , SerializeOptions
  , SerializeRange
  , HTMLSerializeOptions
  , HTMLSerializeRange
  , new
  , activate
  , dispose
  , serialize
  , serializeAsText
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)

-- ============================================================================
-- Types
-- ============================================================================

-- | Foreign type for SerializeAddon instance
foreign import data SerializeAddon :: Type

-- | Foreign type for terminal core
foreign import data ITerminalCore :: Type

-- | Serialize range specification
type SerializeRange =
  { start :: Int
  , end :: Int
  }

-- | Options for serialize function
type SerializeOptions =
  { range :: Maybe SerializeRange
  , scrollback :: Maybe Int
  , excludeModes :: Maybe Boolean
  , excludeAltBuffer :: Maybe Boolean
  }

-- | Range for HTML serialization
type HTMLSerializeRange =
  { startLine :: Int
  , endLine :: Int
  , startCol :: Int
  }

-- | Options for HTML serialization
type HTMLSerializeOptions =
  { scrollback :: Maybe Int
  , onlySelection :: Maybe Boolean
  , includeGlobalBackground :: Maybe Boolean
  , range :: Maybe HTMLSerializeRange
  }

-- | Options for text serialization
type TextSerializeOptions =
  { scrollback :: Maybe Int
  , trimWhitespace :: Maybe Boolean
  }

-- ============================================================================
-- FFI Declarations
-- ============================================================================

foreign import newImpl :: Effect SerializeAddon

foreign import activateImpl :: EffectFn2 SerializeAddon ITerminalCore Unit

foreign import disposeImpl :: EffectFn1 SerializeAddon Unit

foreign import serializeImpl :: EffectFn2 SerializeAddon (SerializeOptionsJS) String

foreign import serializeAsTextImpl :: EffectFn2 SerializeAddon (TextSerializeOptionsJS) String

-- ============================================================================
-- Internal JS-compatible types
-- ============================================================================

type SerializeRangeJS =
  { start :: Int
  , end :: Int
  }

type SerializeOptionsJS =
  { range :: Nullable SerializeRangeJS
  , scrollback :: Nullable Int
  , excludeModes :: Nullable Boolean
  , excludeAltBuffer :: Nullable Boolean
  }

type TextSerializeOptionsJS =
  { scrollback :: Nullable Int
  , trimWhitespace :: Nullable Boolean
  }

-- | Internal nullable type for FFI
foreign import data Nullable :: Type -> Type

foreign import toNullable :: forall a. Maybe a -> Nullable a
foreign import null :: forall a. Nullable a

-- ============================================================================
-- Public API
-- ============================================================================

-- | Create a new SerializeAddon instance
new :: Effect SerializeAddon
new = newImpl

-- | Activate the addon (called by Terminal.loadAddon)
activate :: SerializeAddon -> ITerminalCore -> Effect Unit
activate addon term = runEffectFn2 activateImpl addon term

-- | Dispose the addon and clean up resources
dispose :: SerializeAddon -> Effect Unit
dispose addon = runEffectFn1 disposeImpl addon

-- | Serializes terminal rows into a string that can be written back to the
-- | terminal to restore the state. The cursor will also be positioned to the
-- | correct cell.
serialize :: SerializeAddon -> Maybe SerializeOptions -> Effect String
serialize addon maybeOpts = do
  let jsOpts = case maybeOpts of
        Nothing ->
          { range: null
          , scrollback: null
          , excludeModes: null
          , excludeAltBuffer: null
          }
        Just opts ->
          { range: toNullable (opts.range)
          , scrollback: toNullable opts.scrollback
          , excludeModes: toNullable opts.excludeModes
          , excludeAltBuffer: toNullable opts.excludeAltBuffer
          }
  runEffectFn2 serializeImpl addon jsOpts

-- | Serializes terminal content as plain text (no escape sequences)
serializeAsText :: SerializeAddon -> Maybe TextSerializeOptions -> Effect String
serializeAsText addon maybeOpts = do
  let jsOpts = case maybeOpts of
        Nothing ->
          { scrollback: null
          , trimWhitespace: null
          }
        Just opts ->
          { scrollback: toNullable opts.scrollback
          , trimWhitespace: toNullable opts.trimWhitespace
          }
  runEffectFn2 serializeAsTextImpl addon jsOpts

-- ============================================================================
-- Buffer Types (for reference - matching ghostty-web internal interfaces)
-- ============================================================================

-- | Buffer type enumeration
data BufferType = Normal | Alternate

-- | Buffer cell attributes
type CellAttributes =
  { chars :: String
  , code :: Int
  , width :: Int
  , fgColorMode :: Int
  , bgColorMode :: Int
  , fgColor :: Int
  , bgColor :: Int
  , isBold :: Boolean
  , isItalic :: Boolean
  , isUnderline :: Boolean
  , isStrikethrough :: Boolean
  , isBlink :: Boolean
  , isInverse :: Boolean
  , isInvisible :: Boolean
  , isFaint :: Boolean
  , isDim :: Boolean
  }

-- | Buffer line interface (for documentation)
-- | In actual use, these are accessed via FFI
type BufferLineInfo =
  { length :: Int
  , isWrapped :: Boolean
  }

-- | Buffer interface (for documentation)
type BufferInfo =
  { bufferType :: BufferType
  , cursorX :: Int
  , cursorY :: Int
  , viewportY :: Int
  , baseY :: Int
  , length :: Int
  }

-- ============================================================================
-- Helper Functions (Pure)
-- ============================================================================

-- | Constrain a value between low and high bounds
constrain :: Int -> Int -> Int -> Int
constrain value low high = max low (min value high)

-- | Check if two cells have equal foreground colors
-- | (Implementation in FFI, this is the type signature)
-- foreign import equalFg :: IBufferCell -> IBufferCell -> Boolean

-- | Check if two cells have equal background colors
-- foreign import equalBg :: IBufferCell -> IBufferCell -> Boolean

-- | Check if two cells have equal flags
-- foreign import equalFlags :: IBufferCell -> IBufferCell -> Boolean
