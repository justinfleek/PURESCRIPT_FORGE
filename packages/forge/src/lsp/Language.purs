-- | LSP Language detection
-- | Ported from: opencode-dev/packages/opencode/src/lsp/language.ts
module Forge.LSP.Language 
  ( LanguageInfo
  , detectLanguage
  , supportedLanguages
  , getLanguageById
  , isSupported
  ) where

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
  in Array.find (\lang -> Array.elem lowerExt (map String.toLower lang.extensions)) supportedLanguages
  where
    getFileExtension :: String -> String
    getFileExtension filePath =
      case String.lastIndexOf (String.Pattern ".") filePath of
        Nothing -> ""
        Just idx -> String.drop (idx + 1) filePath

-- | Get language by ID
getLanguageById :: String -> Maybe LanguageInfo
getLanguageById langId = 
  Array.find (\lang -> String.toLower lang.id == String.toLower langId) supportedLanguages

-- | Check if a file extension is supported
isSupported :: String -> Boolean
isSupported ext = 
  let lowerExt = String.toLower ext
  in Array.any (\lang -> Array.elem lowerExt (map String.toLower lang.extensions)) supportedLanguages

-- | Get supported languages
-- | Mirrors the language definitions from lsp/language.ts
supportedLanguages :: Array LanguageInfo
supportedLanguages =
  [ { id: "purescript", name: "PureScript", extensions: ["purs"], serverCommand: Just "purescript-language-server" }
  , { id: "haskell", name: "Haskell", extensions: ["hs", "lhs"], serverCommand: Just "haskell-language-server-wrapper" }
  , { id: "lean4", name: "Lean 4", extensions: ["lean"], serverCommand: Just "lean" }
  , { id: "typescript", name: "TypeScript", extensions: ["ts", "tsx", "mts", "cts"], serverCommand: Just "typescript-language-server" }
  , { id: "javascript", name: "JavaScript", extensions: ["js", "jsx", "mjs", "cjs"], serverCommand: Just "typescript-language-server" }
  , { id: "deno", name: "Deno", extensions: ["ts", "tsx"], serverCommand: Just "deno" }
  , { id: "vue", name: "Vue", extensions: ["vue"], serverCommand: Just "vue-language-server" }
  , { id: "svelte", name: "Svelte", extensions: ["svelte"], serverCommand: Just "svelteserver" }
  , { id: "astro", name: "Astro", extensions: ["astro"], serverCommand: Just "@astrojs/language-server" }
  , { id: "python", name: "Python", extensions: ["py", "pyw", "pyi"], serverCommand: Just "pyright-langserver" }
  , { id: "rust", name: "Rust", extensions: ["rs"], serverCommand: Just "rust-analyzer" }
  , { id: "go", name: "Go", extensions: ["go"], serverCommand: Just "gopls" }
  , { id: "java", name: "Java", extensions: ["java"], serverCommand: Just "jdtls" }
  , { id: "kotlin", name: "Kotlin", extensions: ["kt", "kts"], serverCommand: Just "kotlin-language-server" }
  , { id: "scala", name: "Scala", extensions: ["scala", "sc"], serverCommand: Just "metals" }
  , { id: "cpp", name: "C++", extensions: ["cpp", "cxx", "cc", "hpp", "hxx", "hh"], serverCommand: Just "clangd" }
  , { id: "c", name: "C", extensions: ["c", "h"], serverCommand: Just "clangd" }
  , { id: "csharp", name: "C#", extensions: ["cs"], serverCommand: Just "OmniSharp" }
  , { id: "fsharp", name: "F#", extensions: ["fs", "fsi", "fsx"], serverCommand: Just "fsautocomplete" }
  , { id: "swift", name: "Swift", extensions: ["swift"], serverCommand: Just "sourcekit-lsp" }
  , { id: "ruby", name: "Ruby", extensions: ["rb", "rake", "gemspec"], serverCommand: Just "solargraph" }
  , { id: "elixir", name: "Elixir", extensions: ["ex", "exs"], serverCommand: Just "elixir-ls" }
  , { id: "erlang", name: "Erlang", extensions: ["erl", "hrl"], serverCommand: Just "erlang_ls" }
  , { id: "zig", name: "Zig", extensions: ["zig"], serverCommand: Just "zls" }
  , { id: "nim", name: "Nim", extensions: ["nim", "nims"], serverCommand: Just "nimlsp" }
  , { id: "ocaml", name: "OCaml", extensions: ["ml", "mli"], serverCommand: Just "ocamllsp" }
  , { id: "php", name: "PHP", extensions: ["php"], serverCommand: Just "intelephense" }
  , { id: "lua", name: "Lua", extensions: ["lua"], serverCommand: Just "lua-language-server" }
  , { id: "bash", name: "Bash", extensions: ["sh", "bash"], serverCommand: Just "bash-language-server" }
  , { id: "yaml", name: "YAML", extensions: ["yaml", "yml"], serverCommand: Just "yaml-language-server" }
  , { id: "json", name: "JSON", extensions: ["json", "jsonc"], serverCommand: Just "vscode-json-languageserver" }
  , { id: "toml", name: "TOML", extensions: ["toml"], serverCommand: Just "taplo-lsp" }
  , { id: "terraform", name: "Terraform", extensions: ["tf", "tfvars"], serverCommand: Just "terraform-ls" }
  , { id: "prisma", name: "Prisma", extensions: ["prisma"], serverCommand: Just "prisma-language-server" }
  , { id: "dart", name: "Dart", extensions: ["dart"], serverCommand: Just "dart" }
  , { id: "html", name: "HTML", extensions: ["html", "htm"], serverCommand: Just "vscode-html-languageserver" }
  , { id: "css", name: "CSS", extensions: ["css", "scss", "sass", "less"], serverCommand: Just "vscode-css-languageserver" }
  , { id: "sql", name: "SQL", extensions: ["sql"], serverCommand: Nothing }
  , { id: "markdown", name: "Markdown", extensions: ["md", "markdown"], serverCommand: Nothing }
  , { id: "nix", name: "Nix", extensions: ["nix"], serverCommand: Just "nil" }
  ]
