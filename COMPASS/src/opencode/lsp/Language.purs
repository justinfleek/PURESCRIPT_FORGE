-- | LSP Language detection
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/lsp/language.ts
module Opencode.LSP.Language where

import Prelude
import Data.Maybe (Maybe(..))

-- | Language info
type LanguageInfo =
  { id :: String
  , name :: String
  , extensions :: Array String
  , serverCommand :: Maybe String
  }

-- | Detect language from file path
detectLanguage :: String -> Maybe LanguageInfo
detectLanguage path = Nothing -- TODO: Implement

-- | Get supported languages
supportedLanguages :: Array LanguageInfo
supportedLanguages = [] -- TODO: Populate
