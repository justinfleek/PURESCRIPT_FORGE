-- | FileIcon Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/file-icon.tsx (584 lines)
-- |
-- | File/folder icon based on name and extension.
-- | Pure Halogen implementation - uses SVG sprite references.
-- |
-- | Data Attributes:
-- | - `data-component="file-icon"` - SVG element
module UI.Components.FileIcon
  ( component
  , Input
  , NodeType(..)
  , chooseIconName
  , defaultInput
  ) where

import Prelude

import Data.Array (find)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), drop, lastIndexOf, length, split, toLower)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File node type
data NodeType
  = File
  | Directory

derive instance eqNodeType :: Eq NodeType

-- | FileIcon input props
type Input =
  { path :: String
  , nodeType :: NodeType
  , expanded :: Boolean       -- For directories: open/closed state
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { path: ""
  , nodeType: File
  , expanded: false
  , className: Nothing
  }

-- | Internal state
type State = { input :: Input }

-- | Internal actions
data Action = Receive Input

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState: \input -> { input }
  , render
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let iconName = chooseIconName state.input.path state.input.nodeType state.input.expanded
      spriteUrl = "/file-icons/sprite.svg#" <> iconName
  in
    HH.element (HH.ElemName "svg")
      ([ HP.attr (HH.AttrName "data-component") "file-icon"
       ] <> classAttr state.input.className)
      [ HH.element (HH.ElemName "use")
          [ HP.attr (HH.AttrName "href") spriteUrl ]
          []
      ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ICON SELECTION (Pure Function)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Choose the icon name for a file or directory
-- | This is a pure function - no FFI needed
chooseIconName :: String -> NodeType -> Boolean -> String
chooseIconName path nodeType expanded =
  let baseName = basenameOf path
      baseLower = toLower baseName
  in case nodeType of
    Directory -> chooseDirectoryIcon baseLower expanded
    File -> chooseFileIcon baseLower

-- | Get the basename from a path
basenameOf :: String -> String
basenameOf p =
  let parts = split (Pattern "/") p
  in fromMaybe "" (lastElement parts)

lastElement :: Array String -> Maybe String
lastElement arr = case arr of
  [] -> Nothing
  _ -> Just (unsafeLastImpl arr)

foreign import unsafeLastImpl :: Array String -> String

-- | Choose icon for a directory
chooseDirectoryIcon :: String -> Boolean -> String
chooseDirectoryIcon name expanded =
  let baseIcon = fromMaybe defaultFolderIcon (lookupFolderIcon name)
  in if expanded
     then toOpenVariant baseIcon
     else baseIcon

-- | Choose icon for a file
chooseFileIcon :: String -> String
chooseFileIcon name =
  -- First try exact filename match
  case lookupFileNameIcon name of
    Just icon -> icon
    Nothing ->
      -- Then try extensions (longest first)
      case findExtensionIcon name of
        Just icon -> icon
        Nothing -> defaultFileIcon

-- | Convert folder icon to open variant
toOpenVariant :: String -> String
toOpenVariant icon =
  if startsWith "Folder" icon
    then icon <> "Open"
    else icon

startsWith :: String -> String -> Boolean
startsWith = startsWithImpl

foreign import startsWithImpl :: String -> String -> Boolean

-- | Find extension icon by trying suffixes
findExtensionIcon :: String -> Maybe String
findExtensionIcon name =
  let exts = getDottedSuffixes name
  in findFirst lookupExtensionIcon exts

findFirst :: (String -> Maybe String) -> Array String -> Maybe String
findFirst _ [] = Nothing
findFirst f arr = case f =<< (arrayHeadImpl arr) of
  Just x -> Just x
  Nothing -> findFirst f (arrayTailImpl arr)

foreign import arrayHeadImpl :: forall a. Array a -> Maybe a
foreign import arrayTailImpl :: forall a. Array a -> Array a

-- | Get all dotted suffixes from a filename (longest first)
getDottedSuffixes :: String -> Array String
getDottedSuffixes name = getDottedSuffixesImpl name

foreign import getDottedSuffixesImpl :: String -> Array String

-- ═══════════════════════════════════════════════════════════════════════════════
-- ICON MAPPINGS
-- ═══════════════════════════════════════════════════════════════════════════════

defaultFileIcon :: String
defaultFileIcon = "Document"

defaultFolderIcon :: String
defaultFolderIcon = "Folder"

-- | Lookup file name in mapping
lookupFileNameIcon :: String -> Maybe String
lookupFileNameIcon name = find (\{key, _} -> key == name) fileNameIcons >>= \r -> Just r.icon

-- | Lookup extension in mapping
lookupExtensionIcon :: String -> Maybe String
lookupExtensionIcon ext = find (\{key, _} -> key == ext) extensionIcons >>= \r -> Just r.icon

-- | Lookup folder name in mapping
lookupFolderIcon :: String -> Maybe String
lookupFolderIcon name = 
  let variants = [name, "." <> name, "_" <> name, "__" <> name <> "__"]
  in findFirst lookupSingleFolder variants

lookupSingleFolder :: String -> Maybe String
lookupSingleFolder name = find (\{key, _} -> key == name) folderIcons >>= \r -> Just r.icon

type IconMapping = { key :: String, icon :: String }

-- File name to icon mappings (subset - most common)
fileNameIcons :: Array IconMapping
fileNameIcons =
  [ { key: "readme.md", icon: "Readme" }
  , { key: "changelog.md", icon: "Changelog" }
  , { key: "license", icon: "Certificate" }
  , { key: "package.json", icon: "Nodejs" }
  , { key: "package-lock.json", icon: "Nodejs" }
  , { key: "yarn.lock", icon: "Yarn" }
  , { key: "pnpm-lock.yaml", icon: "Pnpm" }
  , { key: "bun.lock", icon: "Bun" }
  , { key: "bun.lockb", icon: "Bun" }
  , { key: "dockerfile", icon: "Docker" }
  , { key: "docker-compose.yml", icon: "Docker" }
  , { key: "docker-compose.yaml", icon: "Docker" }
  , { key: ".dockerignore", icon: "Docker" }
  , { key: "tsconfig.json", icon: "Tsconfig" }
  , { key: "jsconfig.json", icon: "Jsconfig" }
  , { key: ".eslintrc", icon: "Eslint" }
  , { key: ".eslintrc.js", icon: "Eslint" }
  , { key: ".eslintrc.json", icon: "Eslint" }
  , { key: ".prettierrc", icon: "Prettier" }
  , { key: ".prettierrc.js", icon: "Prettier" }
  , { key: ".prettierrc.json", icon: "Prettier" }
  , { key: "vite.config.js", icon: "Vite" }
  , { key: "vite.config.ts", icon: "Vite" }
  , { key: ".gitignore", icon: "Git" }
  , { key: ".gitattributes", icon: "Git" }
  , { key: "makefile", icon: "Makefile" }
  , { key: "cargo.toml", icon: "Rust" }
  , { key: "go.mod", icon: "GoMod" }
  , { key: "go.sum", icon: "GoMod" }
  , { key: "requirements.txt", icon: "Python" }
  , { key: "pyproject.toml", icon: "Python" }
  , { key: ".env", icon: "Tune" }
  , { key: ".env.local", icon: "Tune" }
  , { key: ".env.development", icon: "Tune" }
  , { key: ".env.production", icon: "Tune" }
  , { key: ".env.example", icon: "Tune" }
  ]

-- Extension to icon mappings (subset - most common)
extensionIcons :: Array IconMapping
extensionIcons =
  [ { key: "spec.ts", icon: "TestTs" }
  , { key: "test.ts", icon: "TestTs" }
  , { key: "spec.tsx", icon: "TestJsx" }
  , { key: "test.tsx", icon: "TestJsx" }
  , { key: "spec.js", icon: "TestJs" }
  , { key: "test.js", icon: "TestJs" }
  , { key: "d.ts", icon: "TypescriptDef" }
  , { key: "ts", icon: "Typescript" }
  , { key: "tsx", icon: "React_ts" }
  , { key: "js", icon: "Javascript" }
  , { key: "jsx", icon: "React" }
  , { key: "mjs", icon: "Javascript" }
  , { key: "cjs", icon: "Javascript" }
  , { key: "html", icon: "Html" }
  , { key: "htm", icon: "Html" }
  , { key: "css", icon: "Css" }
  , { key: "scss", icon: "Sass" }
  , { key: "sass", icon: "Sass" }
  , { key: "less", icon: "Less" }
  , { key: "json", icon: "Json" }
  , { key: "xml", icon: "Xml" }
  , { key: "yml", icon: "Yaml" }
  , { key: "yaml", icon: "Yaml" }
  , { key: "toml", icon: "Toml" }
  , { key: "md", icon: "Markdown" }
  , { key: "mdx", icon: "Mdx" }
  , { key: "py", icon: "Python" }
  , { key: "rs", icon: "Rust" }
  , { key: "go", icon: "Go" }
  , { key: "java", icon: "Java" }
  , { key: "kt", icon: "Kotlin" }
  , { key: "php", icon: "Php" }
  , { key: "rb", icon: "Ruby" }
  , { key: "cs", icon: "Csharp" }
  , { key: "cpp", icon: "Cpp" }
  , { key: "c", icon: "C" }
  , { key: "h", icon: "H" }
  , { key: "swift", icon: "Swift" }
  , { key: "dart", icon: "Dart" }
  , { key: "hs", icon: "Haskell" }
  , { key: "elm", icon: "Elm" }
  , { key: "ex", icon: "Elixir" }
  , { key: "exs", icon: "Elixir" }
  , { key: "sh", icon: "Console" }
  , { key: "bash", icon: "Console" }
  , { key: "zsh", icon: "Console" }
  , { key: "ps1", icon: "Powershell" }
  , { key: "svg", icon: "Svg" }
  , { key: "png", icon: "Image" }
  , { key: "jpg", icon: "Image" }
  , { key: "jpeg", icon: "Image" }
  , { key: "gif", icon: "Image" }
  , { key: "webp", icon: "Image" }
  , { key: "mp4", icon: "Video" }
  , { key: "mp3", icon: "Audio" }
  , { key: "zip", icon: "Zip" }
  , { key: "tar", icon: "Zip" }
  , { key: "gz", icon: "Zip" }
  , { key: "pdf", icon: "Pdf" }
  , { key: "sql", icon: "Database" }
  , { key: "db", icon: "Database" }
  , { key: "log", icon: "Log" }
  , { key: "lock", icon: "Lock" }
  , { key: "graphql", icon: "Graphql" }
  , { key: "gql", icon: "Graphql" }
  , { key: "purs", icon: "Purescript" }
  , { key: "lean", icon: "Lean" }
  , { key: "nix", icon: "Nix" }
  ]

-- Folder name to icon mappings (subset - most common)
folderIcons :: Array IconMapping
folderIcons =
  [ { key: "src", icon: "FolderSrc" }
  , { key: "source", icon: "FolderSrc" }
  , { key: "lib", icon: "FolderLib" }
  , { key: "libs", icon: "FolderLib" }
  , { key: "test", icon: "FolderTest" }
  , { key: "tests", icon: "FolderTest" }
  , { key: "__tests__", icon: "FolderTest" }
  , { key: "spec", icon: "FolderTest" }
  , { key: "specs", icon: "FolderTest" }
  , { key: "node_modules", icon: "FolderNode" }
  , { key: "packages", icon: "FolderPackages" }
  , { key: "build", icon: "FolderBuildkite" }
  , { key: "dist", icon: "FolderDist" }
  , { key: "out", icon: "FolderDist" }
  , { key: "target", icon: "FolderTarget" }
  , { key: "config", icon: "FolderConfig" }
  , { key: "configs", icon: "FolderConfig" }
  , { key: "docker", icon: "FolderDocker" }
  , { key: "docs", icon: "FolderDocs" }
  , { key: "doc", icon: "FolderDocs" }
  , { key: "public", icon: "FolderPublic" }
  , { key: "static", icon: "FolderPublic" }
  , { key: "assets", icon: "FolderImages" }
  , { key: "images", icon: "FolderImages" }
  , { key: "img", icon: "FolderImages" }
  , { key: "fonts", icon: "FolderFont" }
  , { key: "styles", icon: "FolderCss" }
  , { key: "css", icon: "FolderCss" }
  , { key: "components", icon: "FolderComponents" }
  , { key: "views", icon: "FolderViews" }
  , { key: "layouts", icon: "FolderLayout" }
  , { key: "hooks", icon: "FolderHook" }
  , { key: "store", icon: "FolderStore" }
  , { key: "stores", icon: "FolderStore" }
  , { key: "api", icon: "FolderApi" }
  , { key: "routes", icon: "FolderRoutes" }
  , { key: "types", icon: "FolderTypescript" }
  , { key: ".github", icon: "FolderGithub" }
  , { key: ".gitlab", icon: "FolderGitlab" }
  , { key: ".git", icon: "FolderGit" }
  , { key: ".vscode", icon: "FolderVscode" }
  , { key: ".cursor", icon: "FolderCursor" }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- MINIMAL FFI
-- ═══════════════════════════════════════════════════════════════════════════════
-- String/Array utilities
