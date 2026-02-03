-- | Command context - manages keybindings and command palette
-- | Migrated from: forge-dev/packages/app/src/context/command.tsx
module App.Context.Command
  ( Keybind
  , KeybindConfig
  , CommandOption
  , CommandCatalogItem
  , parseKeybind
  , matchKeybind
  , formatKeybind
  , normalizeKey
  , isMac
  , actionId
  ) where

import Prelude

import Data.Array (filter, length, (:))
import Data.Array as Array
import Data.Foldable (any)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split, toLower, trim)
import Data.String as String
import Data.Int (pow)

-- | Keybind configuration string
type KeybindConfig = String

-- | Parsed keybind
type Keybind =
  { key :: String
  , ctrl :: Boolean
  , meta :: Boolean
  , shift :: Boolean
  , alt :: Boolean
  }

-- | Command option for registration
type CommandOption =
  { id :: String
  , title :: String
  , description :: Maybe String
  , category :: Maybe String
  , keybind :: Maybe KeybindConfig
  , slash :: Maybe String
  , suggested :: Maybe Boolean
  , disabled :: Maybe Boolean
  }

-- | Command catalog item for persistence
type CommandCatalogItem =
  { title :: String
  , description :: Maybe String
  , category :: Maybe String
  , keybind :: Maybe KeybindConfig
  , slash :: Maybe String
  }

-- | Suggested prefix for command IDs
suggestedPrefix :: String
suggestedPrefix = "suggested."

-- | Strip suggested prefix from action ID
actionId :: String -> String
actionId id =
  if String.take (String.length suggestedPrefix) id == suggestedPrefix
  then String.drop (String.length suggestedPrefix) id
  else id

-- | Check if running on Mac (would be FFI in real implementation)
isMac :: Boolean
isMac = false  -- Default to non-Mac; real implementation would check navigator.platform

-- | Normalize a key name
normalizeKey :: String -> String
normalizeKey key =
  case key of
    "," -> "comma"
    "+" -> "plus"
    " " -> "space"
    _ -> toLower key

-- | Parse a keybind config string into keybinds
parseKeybind :: KeybindConfig -> Array Keybind
parseKeybind config =
  if config == "" || config == "none"
  then []
  else
    let
      combos = split (Pattern ",") config
    in
      map parseCombo combos
  where
    parseCombo :: String -> Keybind
    parseCombo combo =
      let
        parts = split (Pattern "+") (toLower (trim combo))
      in
        foldlParts { key: "", ctrl: false, meta: false, shift: false, alt: false } parts
    
    foldlParts :: Keybind -> Array String -> Keybind
    foldlParts kb [] = kb
    foldlParts kb (p : rest) =
      let
        kb' = case p of
          "ctrl" -> kb { ctrl = true }
          "control" -> kb { ctrl = true }
          "meta" -> kb { meta = true }
          "cmd" -> kb { meta = true }
          "command" -> kb { meta = true }
          "mod" -> if isMac then kb { meta = true } else kb { ctrl = true }
          "alt" -> kb { alt = true }
          "option" -> kb { alt = true }
          "shift" -> kb { shift = true }
          _ -> kb { key = p }
      in
        foldlParts kb' rest

-- | Check if a keybind matches keyboard event properties
matchKeybind :: Array Keybind -> { key :: String, ctrlKey :: Boolean, metaKey :: Boolean, shiftKey :: Boolean, altKey :: Boolean } -> Boolean
matchKeybind keybinds event =
  let
    eventKey = normalizeKey event.key
  in
    any (\kb ->
      kb.key == eventKey &&
      kb.ctrl == event.ctrlKey &&
      kb.meta == event.metaKey &&
      kb.shift == event.shiftKey &&
      kb.alt == event.altKey
    ) keybinds

-- | Format a keybind for display
formatKeybind :: KeybindConfig -> String
formatKeybind config =
  if config == "" || config == "none"
  then ""
  else
    let
      keybinds = parseKeybind config
    in
      case Array.head keybinds of
        Nothing -> ""
        Just kb -> formatSingle kb
  where
    formatSingle :: Keybind -> String
    formatSingle kb =
      let
        parts = Array.catMaybes
          [ if kb.ctrl then Just (if isMac then "\x2303" else "Ctrl") else Nothing
          , if kb.alt then Just (if isMac then "\x2325" else "Alt") else Nothing
          , if kb.shift then Just (if isMac then "\x21E7" else "Shift") else Nothing
          , if kb.meta then Just (if isMac then "\x2318" else "Meta") else Nothing
          , if kb.key /= "" then Just (formatKey kb.key) else Nothing
          ]
      in
        if isMac
        then String.joinWith "" parts
        else String.joinWith "+" parts
    
    formatKey :: String -> String
    formatKey key =
      case key of
        "arrowup" -> "\x2191"
        "arrowdown" -> "\x2193"
        "arrowleft" -> "\x2190"
        "arrowright" -> "\x2192"
        "comma" -> ","
        "plus" -> "+"
        "space" -> "Space"
        _ -> 
          if String.length key == 1
          then String.toUpper key
          else String.toUpper (String.take 1 key) <> String.drop 1 key
