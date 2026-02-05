-- | Omega Handler Provider Selection
-- | Pure PureScript provider selection logic
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Provider
  ( selectProvider
  , ProviderSelection
  ) where

import Prelude

import Data.Array (filter, concatMap, elem)
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Either (Either(..))
import Data.String as String
import Foreign.Object as Object
import Console.App.Routes.Omega.Util.Error (OmegaError(..), ModelError)
import Console.App.Routes.Omega.Util.Handler.Types (ModelInfo, ProviderData, AuthInfo, RetryOptions)
import Console.App.Routes.Omega.Util.Provider.OpenAI (openaiHelper)
import Console.App.Routes.Omega.Util.Provider.Anthropic (anthropicHelper)
import Console.App.Routes.Omega.Util.Provider.Google (googleHelper)
import Console.App.Routes.Omega.Util.Provider.OpenAICompatible (oaCompatHelper)

-- | Maximum retries before using fallback
maxRetries :: Int
maxRetries = 3

-- | Provider selection result
type ProviderSelection = ProviderData

-- | Omega data with providers
type OmegaDataWithProviders =
  { models :: Object.Object (Array ModelInfo)
  , providers :: Object.Object ProviderData
  }

-- | Select provider for the request
selectProvider ::
  String ->  -- reqModel
  OmegaDataWithProviders ->
  AuthInfo ->
  ModelInfo ->
  String ->  -- sessionId
  Boolean ->  -- isTrial
  RetryOptions ->
  Maybe String ->  -- stickyProvider
  Either OmegaError ProviderSelection
selectProvider reqModel omegaData authInfo modelInfo sessionId isTrial retry stickyProvider =
  case chooseProvider of
    Nothing -> Left $ ModelError "No provider available"
    Just provider ->
      case Object.lookup provider.id omegaData.providers of
        Nothing -> Left $ ModelError $ "Provider " <> provider.id <> " not supported"
        Just providerData -> Right $ mergeProviderData provider providerData reqModel

  where
  chooseProvider :: Maybe ProviderData
  chooseProvider
    | isJust authInfo.provider =
        -- BYOK: use byokProvider
        findProvider modelInfo.providers modelInfo.byokProvider
    | isTrial && isJust modelInfo.trial =
        -- Trial: use trial provider
        findProvider modelInfo.providers (Just modelInfo.trial.provider)
    | isJust stickyProvider && modelInfo.stickyProvider /= Just "strict" =
        -- Sticky: use sticky provider if available
        findProvider modelInfo.providers stickyProvider
    | retry.retryCount >= maxRetries && isJust modelInfo.fallbackProvider =
        -- Max retries: use fallback
        findProvider modelInfo.providers modelInfo.fallbackProvider
    | otherwise =
        -- Weighted random selection
        selectWeightedProvider modelInfo.providers retry.excludeProviders sessionId

-- | Find provider by ID
findProvider :: Array ProviderData -> Maybe String -> Maybe ProviderData
findProvider providers (Just id) = Array.find (\p -> p.id == id) providers
findProvider _ Nothing = Nothing

-- | Select provider using weighted random selection
selectWeightedProvider ::
  Array ProviderData ->
  Array String ->  -- excludeProviders
  String ->  -- sessionId
  Maybe ProviderData
selectWeightedProvider providers excludeProviders sessionId =
  let
    available = filter (\p -> not p.disabled && not (p.id `elem` excludeProviders)) providers
    weighted = concatMap (\p -> replicate (fromMaybe 1 p.weight) p) available
  in
    if Array.length weighted == 0
      then Nothing
      else Array.index weighted (hashSessionId sessionId `mod` Array.length weighted)

-- | Hash last 4 characters of session ID for provider selection
hashSessionId :: String -> Int
hashSessionId sessionId =
  let
    len = String.length sessionId
    start = max 0 (len - 4)
    suffix = String.drop start sessionId
    chars = toCharArray suffix
  in
    Array.foldl (\h c -> (h * 31 + charCode c) `mod` 2147483647) 0 chars

-- | Replicate element n times
replicate :: Int -> ProviderData -> Array ProviderData
replicate n x = if n <= 0 then [] else Array.replicate n x

-- | Convert string to char array (FFI)
foreign import toCharArray :: String -> Array Char

-- | Get character code (FFI - converts Char to Int)
foreign import charCode :: Char -> Int

-- | Max helper
max :: Int -> Int -> Int
max a b = if a > b then a else b

-- | Merge provider data with model provider config and add helper methods
mergeProviderData :: ProviderData -> ProviderData -> String -> ProviderData
mergeProviderData modelProvider baseProvider reqModel =
  let
    helperMethods = getProviderHelper baseProvider.format reqModel modelProvider.model
  in
    baseProvider
      { id = modelProvider.id
      , format = baseProvider.format
      , api = baseProvider.api
      , model = modelProvider.model
      , weight = modelProvider.weight
      , disabled = baseProvider.disabled || modelProvider.disabled
      , headerMappings = baseProvider.headerMappings
      , streamSeparator = helperMethods.streamSeparator
      , storeModel = modelProvider.storeModel
      , apiKey = ""  -- Will be set by updateProviderKey
      , modifyUrl = helperMethods.modifyUrl
      , modifyHeaders = helperMethods.modifyHeaders
      , modifyBody = helperMethods.modifyBody
      , createBinaryStreamDecoder = helperMethods.createBinaryStreamDecoder
      , createUsageParser = helperMethods.createUsageParser
      , normalizeUsage = helperMethods.normalizeUsage
      }

-- | Get provider helper methods based on format
getProviderHelper :: String -> String -> String -> ProviderHelperMethods
getProviderHelper format reqModel providerModel =
  case format of
    "anthropic" -> anthropicHelper { reqModel, providerModel }
    "google" -> googleHelper { reqModel, providerModel }
    "openai" -> openaiHelper { reqModel, providerModel }
    _ -> oaCompatHelper { reqModel, providerModel }

-- | Provider helper methods type
type ProviderHelperMethods =
  { modifyUrl :: String -> Maybe Boolean -> String
  , modifyHeaders :: String -> String -> Unit  -- body, apiKey (headers accessed via global)
  , modifyBody :: String -> String
  , createBinaryStreamDecoder :: Unit -> Maybe (String -> Maybe String)
  , streamSeparator :: String
  , createUsageParser :: Unit -> UsageParser
  , normalizeUsage :: String -> UsageInfo
  }

-- | Usage parser type
type UsageParser =
  { parse :: String -> Unit
  , retrieve :: Unit -> Maybe String
  }

import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
