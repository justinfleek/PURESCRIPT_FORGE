-- | Omega Handler Main Function
-- | Orchestrates the Omega API request handling
-- | Pure PureScript - FFI only at boundaries
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Main
  ( handleOmegaRequest
  , HandlerOptions
  , RequestHeaders
  , RequestBody
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array (filter, find)
import Data.String as String
import Foreign.Object as Object
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Omega.Util.Error (OmegaError, getErrorType, getErrorMessage)
import Console.App.Routes.Omega.Util.Handler.Types (AuthInfo, ModelInfo, ProviderData, RetryOptions, BillingSource, CostInfo)
import Console.App.Routes.Omega.Util.Handler.Validation (validateModel, validateBilling, validateModelSettings)
import Console.App.Routes.Omega.Util.Handler.Provider (selectProvider)
import Console.App.Routes.Omega.Util.Handler.Auth (authenticate)
import Console.App.Routes.Omega.Util.Handler.Cost (calculateCost)
import Console.App.Routes.Omega.Util.Handler.Reload (checkReload)
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo, createBodyConverter, createStreamPartConverter, createResponseConverter, normalizeUsage, parseProviderFormat, ProviderFormat(..))

-- | Handler options - all pure PureScript types
type HandlerOptions =
  { format :: String  -- "anthropic" | "openai" | "oa-compat" | "google"
  , parseApiKey :: RequestHeaders -> Maybe String
  , parseModel :: String -> RequestBody -> String
  , parseIsStream :: String -> RequestBody -> Boolean
  }

-- | Pure PureScript types (no Foreign)
-- | Exported for use by route handlers
type RequestHeaders = Array { key :: String, value :: String }
type RequestBody = String
type OmegaData = { models :: Object.Object (Array ModelInfo), providers :: Object.Object ProviderData }
type HttpResponse = { status :: Int, statusText :: String, headers :: RequestHeaders, body :: String }
type DataDumper = { provideModel :: String -> Aff Unit, provideRequest :: String -> Aff Unit, provideResponse :: String -> Aff Unit, provideStream :: String -> Aff Unit, flush :: Aff Unit }
type TrialLimiter = { isTrial :: Aff Boolean, track :: UsageInfo -> Aff Unit }
type RateLimiter = { check :: Aff Unit, track :: Aff Unit }
type StickyTracker = { get :: Aff (Maybe String), set :: String -> Aff Unit }

-- | Main handler function
handleOmegaRequest ::
  APIEvent ->
  HandlerOptions ->
  Aff Response
handleOmegaRequest event opts = do
  -- Extract request data (FFI boundary - converts APIEvent to PureScript types)
  { url, body, headers } <- extractRequestData event
  
  let
    model = opts.parseModel url body
    isStream = opts.parseIsStream url body
    apiKey = opts.parseApiKey headers
    ip = findHeader "x-real-ip" headers
    sessionId = findHeader "x-opencode-session" headers
    requestId = findHeader "x-opencode-request" headers
    projectId = findHeader "x-opencode-project" headers
    ocClient = findHeader "x-opencode-client" headers
  
  -- Log metrics
  logMetric { isStream, session: sessionId, request: requestId, client: ocClient }
  
  -- Get Omega data (FFI boundary)
  omegaData <- getOmegaData
  
  -- Validate model
  modelInfo <- case validateModel omegaData model opts.format of
    Left err -> handleError err
    Right info -> pure info
  
  -- Initialize helpers (FFI boundary)
  dataDumper <- createDataDumper sessionId requestId projectId
  trialLimiter <- createTrialLimiter modelInfo.trial ip ocClient
  isTrial <- trialLimiter.isTrial
  rateLimiter <- createRateLimiter modelInfo.rateLimit ip
  rateLimiter.check
  stickyTracker <- createStickyTracker modelInfo.stickyProvider sessionId
  stickyProvider <- stickyTracker.get
  
  -- Authenticate
  authInfo <- case authenticate modelInfo apiKey of
    Left err -> handleError err
    Right info -> pure info
  
  -- Validate billing
  billingSource <- case validateBilling authInfo modelInfo of
    Left err -> handleError err
    Right source -> pure source
  
  -- Process request with retries
  requestResult <- retriableRequest
    model
    omegaData
    authInfo
    modelInfo
    sessionId
    isTrial
    { excludeProviders: [], retryCount: 0 }
    stickyProvider
    isStream
    body
    headers
    opts
  
  let { providerInfo, reqBody, res, startTimestamp } = requestResult
  
  -- Store model request
  dataDumper.provideModel providerInfo.storeModel
  dataDumper.provideRequest reqBody
  
  -- Store sticky provider
  stickyTracker.set providerInfo.id
  
  -- Handle response
  if isStream
    then handleStreamingResponse providerInfo opts.format res startTimestamp authInfo modelInfo billingSource dataDumper trialLimiter rateLimiter
    else handleNonStreamingResponse providerInfo opts.format res authInfo modelInfo billingSource dataDumper trialLimiter rateLimiter

  where
  -- Retriable request function (pure PureScript)
  retriableRequest ::
    String ->
    OmegaData ->
    Maybe AuthInfo ->
    ModelInfo ->
    String ->
    Boolean ->
    RetryOptions ->
    Maybe String ->
    Boolean ->
    RequestBody ->
    RequestHeaders ->
    HandlerOptions ->
    Aff { providerInfo :: ProviderData, reqBody :: String, res :: HttpResponse, startTimestamp :: Int }
  retriableRequest reqModel omegaData authInfo modelInfo sessionId isTrial retry stickyProvider isStream body headers opts = do
    -- Select provider (pure PureScript)
    providerSelection <- case selectProvider reqModel omegaData authInfo modelInfo sessionId isTrial retry stickyProvider of
      Left err -> handleError err
      Right provider -> pure provider
    
    -- Validate model settings
    case validateModelSettings authInfo of
      Left err -> handleError err
      Right _ -> pure unit
    
    -- Update provider key if BYOK
    let providerInfo = updateProviderKey authInfo providerSelection
    
    -- Log provider
    logMetric { provider: providerInfo.id }
    
    -- Build request (pure PureScript - uses provider helper methods)
    startTimestamp <- getCurrentTime
    let reqUrl = providerInfo.modifyUrl providerInfo.api (Just isStream)
    -- Convert body format if needed
    let inputFormat = fromMaybe OpenAI $ parseProviderFormat opts.format
    let outputFormat = fromMaybe OpenAI $ parseProviderFormat providerInfo.format
    let commonRequest = createBodyConverter inputFormat outputFormat (parseJson body)
    let providerRequestJson = convertToProviderRequest providerInfo.format (stringifyJson commonRequest) providerInfo.model
    let reqBody = providerInfo.modifyBody providerRequestJson
    
    logDebug $ "REQUEST URL: " <> reqUrl
    logDebug $ "REQUEST: " <> String.take 300 reqBody <> "..."
    
    -- Modify headers using provider helper (mutates headers via FFI)
    modifiedHeaders <- modifyHeadersFFI headers reqBody providerInfo.apiKey (\body apiKey -> providerInfo.modifyHeaders body apiKey)
    
    -- Make HTTP request (FFI boundary - external HTTP)
    res <- fetchProviderRequest reqUrl reqBody modifiedHeaders providerInfo
    
    -- Check if retry needed (pure PureScript logic)
    if shouldRetryLogic res.status modelInfo providerInfo
      then retriableRequest
        reqModel
        omegaData
        authInfo
        modelInfo
        sessionId
        isTrial
        { excludeProviders: retry.excludeProviders <> [providerInfo.id], retryCount: retry.retryCount + 1 }
        stickyProvider
        isStream
        body
        headers
        opts
      else pure { providerInfo, reqBody, res, startTimestamp }
  
  -- Handle non-streaming response (pure PureScript)
  handleNonStreamingResponse ::
    ProviderData ->
    String ->
    HttpResponse ->
    Maybe AuthInfo ->
    ModelInfo ->
    BillingSource ->
    DataDumper ->
    TrialLimiter ->
    RateLimiter ->
    Aff Response
  handleNonStreamingResponse providerInfo format res authInfo modelInfo billingSource dataDumper trialLimiter rateLimiter = do
    let responseConverter = createResponseConverter providerInfo.format format
    let json = parseJson res.body
    let convertedJson = responseConverter json
    let body = stringifyJson convertedJson
    
    logMetric { response_length: String.length body }
    logDebug $ "RESPONSE: " <> body
    
    dataDumper.provideResponse body
    dataDumper.flush
    
    let usageJson = extractUsageFromResponse providerInfo.format json
    let usage = providerInfo.normalizeUsage usageJson
    trialLimiter.track usage
    rateLimiter.track
    
    costInfo <- trackUsage authInfo modelInfo providerInfo billingSource usage
    checkReload authInfo costInfo
    
    let resStatus = normalizeResponseStatus res.status
    let resHeaders = scrubResponseHeaders res.headers
    
    createResponse body resStatus res.statusText resHeaders
  
  -- Handle streaming response (pure PureScript + FFI for stream)
  handleStreamingResponse ::
    ProviderData ->
    String ->
    HttpResponse ->
    Int ->
    Maybe AuthInfo ->
    ModelInfo ->
    BillingSource ->
    DataDumper ->
    TrialLimiter ->
    RateLimiter ->
    Aff Response
  handleStreamingResponse providerInfo format res startTimestamp authInfo modelInfo billingSource dataDumper trialLimiter rateLimiter = do
    let streamConverter = createStreamPartConverter providerInfo.format format
    
    -- Create stream (FFI boundary - ReadableStream)
    stream <- createStream
      providerInfo
      streamConverter
      format
      startTimestamp
      dataDumper
      trialLimiter
      rateLimiter
      authInfo
      modelInfo
      billingSource
      res.body
    
    let resStatus = normalizeResponseStatus res.status
    let resHeaders = scrubResponseHeaders res.headers
    
    createStreamResponse stream resStatus res.statusText resHeaders
  
  -- Error handling (pure PureScript)
  handleError :: OmegaError -> Aff a
  handleError err = do
    logMetric { "error.type": getErrorType err, "error.message": getErrorMessage err }
    errorResponse <- createErrorResponse err
    throwErrorResponse errorResponse
  
  -- Pure PureScript helper functions
  findHeader :: String -> RequestHeaders -> String
  findHeader key headers =
    case find (\h -> String.toLower h.key == String.toLower key) headers of
      Just h -> h.value
      Nothing -> ""
  
  
  normalizeResponseStatus :: Int -> Int
  normalizeResponseStatus status = if status == 404 then 400 else status
  
  scrubResponseHeaders :: RequestHeaders -> RequestHeaders
  scrubResponseHeaders headers =
    let keepHeaders = ["content-type", "cache-control"]
    in filter (\h -> elem (String.toLower h.key) keepHeaders) headers
  
  shouldRetryLogic :: Int -> ModelInfo -> ProviderData -> Boolean
  shouldRetryLogic status modelInfo providerInfo =
    status /= 200 &&
    status /= 404 &&
    modelInfo.stickyProvider /= Just "strict" &&
    isJust modelInfo.fallbackProvider &&
    providerInfo.id /= fromMaybe "" modelInfo.fallbackProvider
  
  
  -- Type aliases (pure PureScript)
  type JsonValue = String  -- JSON string representation
  type StreamResponse = String  -- ReadableStream handle (FFI only)
  
  -- Pure PureScript helper
  fromMaybe :: forall a. a -> Maybe a -> a
  fromMaybe default Nothing = default
  fromMaybe _ (Just x) = x
  
  isJust :: forall a. Maybe a -> Boolean
  isJust Nothing = false
  isJust (Just _) = true
  
  -- FFI ONLY at boundaries - converts to/from PureScript types immediately
  foreign import extractRequestData :: APIEvent -> Aff { url :: String, body :: RequestBody, headers :: RequestHeaders }
  foreign import getOmegaData :: Aff OmegaData
  foreign import createDataDumper :: String -> String -> String -> Aff DataDumper
  foreign import createTrialLimiter :: Maybe { provider :: String } -> String -> String -> Aff TrialLimiter
  foreign import createRateLimiter :: Maybe Int -> String -> Aff RateLimiter
  foreign import createStickyTracker :: Maybe String -> String -> Aff StickyTracker
  foreign import getCurrentTime :: Aff Int
  foreign import fetchProviderRequest :: String -> String -> RequestHeaders -> ProviderData -> Aff HttpResponse
  foreign import extractUsageFromResponse :: String -> JsonValue -> String
  foreign import convertToProviderRequest :: String -> JsonValue -> String -> JsonValue
  foreign import modifyHeadersFFI :: RequestHeaders -> String -> String -> (String -> String -> String -> Unit) -> Aff RequestHeaders
  foreign import trackUsage :: Maybe AuthInfo -> ModelInfo -> ProviderData -> BillingSource -> UsageInfo -> Aff CostInfo
  foreign import createResponse :: String -> Int -> String -> RequestHeaders -> Aff Response
  foreign import createStream :: ProviderData -> (JsonValue -> JsonValue) -> String -> Int -> DataDumper -> TrialLimiter -> RateLimiter -> Maybe AuthInfo -> ModelInfo -> BillingSource -> String -> Aff StreamResponse
  foreign import createStreamResponse :: StreamResponse -> Int -> String -> RequestHeaders -> Aff Response
  foreign import createErrorResponse :: OmegaError -> Aff Response
  foreign import throwErrorResponse :: Response -> Aff a
  foreign import updateProviderKey :: Maybe AuthInfo -> ProviderData -> ProviderData
  foreign import parseJson :: String -> JsonValue
  foreign import stringifyJson :: JsonValue -> String
  foreign import logMetric :: { isStream :: Boolean, session :: String, request :: String, client :: String } -> Aff Unit
  foreign import logDebug :: String -> Aff Unit
  
  import Data.Array (elem)
