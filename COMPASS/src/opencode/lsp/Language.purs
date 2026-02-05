-- | LSP Language detection
module Opencode.LSP.Language where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.String as String

-- | Language info
type LanguageInfo =
  { id :: String
  , name :: String
  , extensions :: Array String
  , serverCommand :: Maybe String
  }

-- | Detect language from file path
detectLanguage :: String -> Maybe LanguageInfo
detectLanguage path =
  let extension = getFileExtension path
      lowerExt = String.toLower extension
  in Array.find (\lang -> Array.elem lowerExt (Array.map String.toLower lang.extensions)) supportedLanguages
  where
    getFileExtension :: String -> String
    getFileExtension filePath =
      case String.lastIndexOf (String.Pattern ".") filePath of
        Nothing -> ""
        Just idx -> String.drop (idx + 1) filePath

-- | Get supported languages
supportedLanguages :: Array LanguageInfo
supportedLanguages =
  [ { id: "purescript", name: "PureScript", extensions: ["purs"], serverCommand: Just "purescript-language-server" }
  , { id: "haskell", name: "Haskell", extensions: ["hs", "lhs"], serverCommand: Just "haskell-language-server" }
  , { id: "lean4", name: "Lean 4", extensions: ["lean"], serverCommand: Just "lean" }
  , { id: "typescript", name: "TypeScript", extensions: ["ts", "tsx"], serverCommand: Just "typescript-language-server" }
  , { id: "javascript", name: "JavaScript", extensions: ["js", "jsx"], serverCommand: Just "typescript-language-server" }
  , { id: "python", name: "Python", extensions: ["py"], serverCommand: Just "pylsp" }
  , { id: "rust", name: "Rust", extensions: ["rs"], serverCommand: Just "rust-analyzer" }
  , { id: "go", name: "Go", extensions: ["go"], serverCommand: Just "gopls" }
  , { id: "java", name: "Java", extensions: ["java"], serverCommand: Just "jdtls" }
  , { id: "kotlin", name: "Kotlin", extensions: ["kt"], serverCommand: Just "kotlin-language-server" }
  , { id: "scala", name: "Scala", extensions: ["scala"], serverCommand: Just "metals" }
  , { id: "cpp", name: "C++", extensions: ["cpp", "cxx", "cc", "hpp"], serverCommand: Just "clangd" }
  , { id: "c", name: "C", extensions: ["c", "h"], serverCommand: Just "clangd" }
  ]
