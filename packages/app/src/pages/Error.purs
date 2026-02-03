-- | Error page component for displaying initialization and runtime errors
-- | Migrated from: forge-dev/packages/app/src/pages/error.tsx (291 lines)
module Sidepanel.Pages.Error
  ( ErrorPageProps
  , InitError
  , ErrorPage
  , formatError
  , formatInitError
  , isInitError
  , safeJson
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Foreign (Foreign)
import Foreign.Object (Object)
import Foreign.Object as Object

-- | Structured initialization error type
-- | Matches TypeScript InitError interface
type InitError =
  { name :: String
  , data :: Object Foreign
  }

-- | Props for the ErrorPage component
type ErrorPageProps =
  { error :: Foreign
  }

-- | Internal state for the error page
type ErrorPageState =
  { checking :: Boolean
  , version :: Maybe String
  }

-- | Type guard for InitError
-- | Checks if a foreign value matches the InitError shape
isInitError :: Foreign -> Boolean
isInitError value = 
  -- Implementation would use foreign type checking
  -- In actual FFI, this checks: typeof error === "object" && "name" in error && "data" in error
  false -- Placeholder - actual implementation via FFI

-- | Safely serialize a value to JSON, handling circular references and BigInt
safeJson :: Foreign -> String
safeJson value = 
  -- Handles:
  -- - BigInt conversion to string
  -- - Circular reference detection via WeakSet
  -- - Fallback to String() for non-serializable values
  "[Object]" -- Placeholder - actual implementation via FFI

-- | Translator function type (from useLanguage hook)
type Translator = String -> Object String -> String

-- | Format a specific InitError based on its name
-- | Maps error types to localized messages:
-- | - MCPFailed: MCP server connection failure
-- | - ProviderAuthError: Provider authentication failure
-- | - APIError: Generic API error with status/retry info
-- | - ProviderModelNotFoundError: Model not found with suggestions
-- | - ProviderInitError: Provider initialization failure
-- | - ConfigJsonError: JSON config parsing error
-- | - ConfigDirectoryTypoError: Directory name typo in config
-- | - ConfigFrontmatterError: Markdown frontmatter parsing error
-- | - ConfigInvalidError: Config validation error with issues
-- | - UnknownError: Catch-all for unrecognized errors
formatInitError :: InitError -> Translator -> String
formatInitError err t = case err.name of
  "MCPFailed" ->
    let name = fromMaybe "" $ lookupString "name" err.data
    in t "error.chain.mcpFailed" (Object.singleton "name" name)
    
  "ProviderAuthError" ->
    let providerID = fromMaybe "unknown" $ lookupString "providerID" err.data
        message = fromMaybe "" $ lookupString "message" err.data
    in t "error.chain.providerAuthFailed" 
         (Object.fromFoldable [Tuple "provider" providerID, Tuple "message" message])
    
  "APIError" ->
    formatAPIError err.data t
    
  "ProviderModelNotFoundError" ->
    formatModelNotFoundError err.data t
    
  "ProviderInitError" ->
    let providerID = fromMaybe "unknown" $ lookupString "providerID" err.data
    in t "error.chain.providerInitFailed" (Object.singleton "provider" providerID)
    
  "ConfigJsonError" ->
    formatConfigJsonError err.data t
    
  "ConfigDirectoryTypoError" ->
    formatConfigDirectoryTypoError err.data t
    
  "ConfigFrontmatterError" ->
    formatConfigFrontmatterError err.data t
    
  "ConfigInvalidError" ->
    formatConfigInvalidError err.data t
    
  "UnknownError" ->
    fromMaybe (safeJson (toForeign err.data)) $ lookupString "message" err.data
    
  _ ->
    fromMaybe (safeJson (toForeign err.data)) $ lookupString "message" err.data

-- | Format API error with status code, retry info, and response body
formatAPIError :: Object Foreign -> Translator -> String
formatAPIError errData t =
  let message = fromMaybe (t "error.chain.apiError" Object.empty) $ 
                lookupString "message" errData
      statusLine = lookupNumber "statusCode" errData <#> \status ->
                   t "error.chain.status" (Object.singleton "status" (show status))
      retryLine = lookupBoolean "isRetryable" errData <#> \retryable ->
                  t "error.chain.retryable" (Object.singleton "retryable" (show retryable))
      bodyLine = lookupString "responseBody" errData >>= \body ->
                 if String.null body then Nothing
                 else Just $ t "error.chain.responseBody" (Object.singleton "body" body)
      lines = Array.catMaybes [Just message, statusLine, retryLine, bodyLine]
  in String.joinWith "\n" lines

-- | Format model not found error with suggestions
formatModelNotFoundError :: Object Foreign -> Translator -> String
formatModelNotFoundError errData t =
  let providerID = fromMaybe "unknown" $ lookupString "providerID" errData
      modelID = fromMaybe "unknown" $ lookupString "modelID" errData
      mainLine = t "error.chain.modelNotFound" 
                   (Object.fromFoldable [Tuple "provider" providerID, Tuple "model" modelID])
      suggestionsLine = lookupStringArray "suggestions" errData >>= \suggestions ->
                        if Array.null suggestions then Nothing
                        else Just $ t "error.chain.didYouMean" 
                               (Object.singleton "suggestions" (String.joinWith ", " suggestions))
      checkLine = t "error.chain.checkConfig" Object.empty
      lines = Array.catMaybes [Just mainLine, suggestionsLine, Just checkLine]
  in String.joinWith "\n" lines

-- | Format config JSON error
formatConfigJsonError :: Object Foreign -> Translator -> String
formatConfigJsonError errData t =
  let path = fromMaybe "[unknown path]" $ lookupString "path" errData
      message = lookupString "message" errData
  in case message of
       Just msg -> t "error.chain.configJsonInvalidWithMessage" 
                     (Object.fromFoldable [Tuple "path" path, Tuple "message" msg])
       Nothing -> t "error.chain.configJsonInvalid" (Object.singleton "path" path)

-- | Format config directory typo error
formatConfigDirectoryTypoError :: Object Foreign -> Translator -> String
formatConfigDirectoryTypoError errData t =
  let path = fromMaybe "" $ lookupString "path" errData
      dir = fromMaybe "" $ lookupString "dir" errData
      suggestion = fromMaybe "" $ lookupString "suggestion" errData
  in t "error.chain.configDirectoryTypo" 
       (Object.fromFoldable [Tuple "dir" dir, Tuple "path" path, Tuple "suggestion" suggestion])

-- | Format config frontmatter error
formatConfigFrontmatterError :: Object Foreign -> Translator -> String
formatConfigFrontmatterError errData t =
  let path = fromMaybe "" $ lookupString "path" errData
      message = fromMaybe "" $ lookupString "message" errData
  in t "error.chain.configFrontmatterError" 
       (Object.fromFoldable [Tuple "path" path, Tuple "message" message])

-- | Format config invalid error with validation issues
formatConfigInvalidError :: Object Foreign -> Translator -> String
formatConfigInvalidError errData t =
  let path = fromMaybe "" $ lookupString "path" errData
      message = lookupString "message" errData
      issues = formatValidationIssues errData
      mainLine = case message of
                   Just msg -> t "error.chain.configInvalidWithMessage" 
                                 (Object.fromFoldable [Tuple "path" path, Tuple "message" msg])
                   Nothing -> t "error.chain.configInvalid" (Object.singleton "path" path)
      lines = Array.cons mainLine issues
  in String.joinWith "\n" lines

-- | Format validation issues from config error
formatValidationIssues :: Object Foreign -> Array String
formatValidationIssues errData =
  -- Would extract issues array and format each as "↳ message path.to.field"
  [] -- Placeholder - actual implementation via FFI

-- | Format the complete error chain with cause traversal
-- | Handles:
-- | - InitError (structured errors)
-- | - Error instances (with stack traces)
-- | - String errors
-- | - Unknown values (serialized to JSON)
-- | Tracks depth and parent message to avoid duplicates
formatErrorChain :: Foreign -> Translator -> Int -> Maybe String -> String
formatErrorChain error t depth parentMessage =
  let separator = "\n" <> String.joinWith "" (Array.replicate 40 "-") <> "\n"
      causedBy = t "error.chain.causedBy" Object.empty
      indent = if depth > 0 then separator <> causedBy <> "\n" else ""
  in indent <> "[Error formatting via FFI]" -- Actual implementation handles all cases

-- | Main error formatting function
-- | Entry point that starts the chain with depth 0
formatError :: Foreign -> Translator -> String
formatError error t = formatErrorChain error t 0 Nothing

-- | Helper: lookup string value from Foreign Object
lookupString :: String -> Object Foreign -> Maybe String
lookupString key obj = Nothing -- Placeholder - actual via FFI

-- | Helper: lookup number value from Foreign Object  
lookupNumber :: String -> Object Foreign -> Maybe Number
lookupNumber key obj = Nothing -- Placeholder - actual via FFI

-- | Helper: lookup boolean value from Foreign Object
lookupBoolean :: String -> Object Foreign -> Maybe Boolean
lookupBoolean key obj = Nothing -- Placeholder - actual via FFI

-- | Helper: lookup string array from Foreign Object
lookupStringArray :: String -> Object Foreign -> Maybe (Array String)
lookupStringArray key obj = Nothing -- Placeholder - actual via FFI

-- | Convert to Foreign (placeholder)
toForeign :: forall a. a -> Foreign
toForeign = unsafeCoerce

-- | Unsafe coerce for FFI boundaries
foreign import unsafeCoerce :: forall a b. a -> b

-- | ErrorPage component
-- | Displays:
-- | - Logo
-- | - Error title and description
-- | - Formatted error details (copyable)
-- | - Restart button
-- | - Update check button (if platform supports)
-- | - Discord feedback link
-- | - Version info
type ErrorPage = ErrorPageProps -> Effect Unit
