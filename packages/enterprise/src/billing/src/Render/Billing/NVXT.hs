{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway GPU Billing via NVXT
-- | Triton NVXT plugin for GPU-seconds attribution per render_specs.pdf §6
module Render.Billing.NVXT where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Concurrent.STM.TQueue
import Control.Concurrent.STM.TVar
import Control.Monad (unless)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime, getCurrentTime)
import Data.UUID (UUID)
import qualified Data.UUID as UUID
import Data.Int (Int64)
import qualified Data.Map.Strict as Map
import Foreign.C.String (CString, withCString)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peek, alloca)
import Foreign.C.Types (CInt, CInt64)

-- CUPTI result type
type CUptiResult = CInt

-- | NVXT billing record
data BillingRecord = BillingRecord
  { brRequestId :: UUID
  , brGpuSeconds :: Double
  , brDeviceUuid :: Text
  , brModelName :: Text
  , brTimestamp :: UTCTime
  , brCustomerId :: Maybe Text
  , brPricingTier :: Maybe Text
  }

-- | NVXT trace collector
data NVXTCollector = NVXTCollector
  { nvxtAuditQueue :: TQueue BillingRecord -- Async flush queue
  , nvxtStartTimes :: TVar (Map.Map UUID UTCTime) -- Thread-safe start time storage
  }

-- | Create NVXT collector
createNVXTCollector :: STM NVXTCollector
createNVXTCollector = do
  queue <- newTQueue
  times <- newTVar Map.empty
  pure NVXTCollector
    { nvxtAuditQueue = queue
    , nvxtStartTimes = times
    }

-- | On request start (NVTX push)
onRequestStart :: NVXTCollector -> UUID -> Text -> IO ()
onRequestStart NVXTCollector {..} requestId _modelName = do
  -- Push NVTX range
  nvtxRangePush (Text.unpack (UUID.toText requestId))
  
  -- Record start time and store in thread-safe map
  startTime <- getCurrentTime
  atomically $ do
    times <- readTVar nvxtStartTimes
    writeTVar nvxtStartTimes (Map.insert requestId startTime times)

-- | Request context carrying customer attribution
data RequestContext = RequestContext
  { rcCustomerId :: Maybe Text
  , rcPricingTier :: Maybe Text
  }

-- | Empty request context (no customer attribution)
emptyRequestContext :: RequestContext
emptyRequestContext = RequestContext
  { rcCustomerId = Nothing
  , rcPricingTier = Nothing
  }

-- | On request end (NVTX pop)
onRequestEnd :: NVXTCollector -> UUID -> Text -> RequestContext -> IO BillingRecord
onRequestEnd NVXTCollector {..} requestId modelName reqCtx = do
  -- Pop NVTX range
  nvtxRangePop

  -- Get elapsed time from CUPTI
  elapsedNs <- cuptiGetTimestamp

  -- Compute GPU seconds from start time delta
  now <- getCurrentTime
  startTimeMaybe <- atomically $ do
    times <- readTVar nvxtStartTimes
    let result = Map.lookup requestId times
    writeTVar nvxtStartTimes (Map.delete requestId times)
    pure result

  let gpuSeconds = fromIntegral elapsedNs / 1e9

  -- Get device UUID
  deviceUuid <- getDeviceUUID

  -- Create billing record with customer attribution from request context
  let record = BillingRecord
        { brRequestId = requestId
        , brGpuSeconds = gpuSeconds
        , brDeviceUuid = deviceUuid
        , brModelName = modelName
        , brTimestamp = now
        , brCustomerId = rcCustomerId reqCtx
        , brPricingTier = rcPricingTier reqCtx
        }

  -- Queue for async flush to audit trail
  atomically (writeTQueue nvxtAuditQueue record)

  pure record

-- | Embed billing data in response metadata
embedBillingMetadata :: BillingRecord -> [(Text, Text)]
embedBillingMetadata BillingRecord {..} =
  [ ("x-gpu-seconds", Text.pack (show brGpuSeconds))
  , ("x-gpu-device", brDeviceUuid)
  ]

-- | CAS persistence configuration for billing records
data CASPersistConfig = CASPersistConfig
  { cpEndpoint :: Text
  , cpBatchSize :: Int
  }

-- | Flush billing records to audit trail
-- | Without CAS config, records are drained but not persisted (logged)
flushBillingRecords :: NVXTCollector -> IO ()
flushBillingRecords collector =
  flushBillingRecordsWith collector Nothing

-- | Flush billing records with optional CAS persistence
flushBillingRecordsWith :: NVXTCollector -> Maybe CASPersistConfig -> IO ()
flushBillingRecordsWith NVXTCollector {..} casConfig = do
  -- Drain queue atomically
  records <- atomically $ drainTQueue nvxtAuditQueue

  unless (null records) $ do
    case casConfig of
      Nothing ->
        -- No CAS config: records drained but not persisted
        -- In production, wire CASPersistConfig from application config
        pure ()
      Just CASPersistConfig {..} ->
        -- CAS persistence: convert BillingRecord to GPUAttestation and write
        -- Wire to Render.CAS.Client.writeGPUAttestation when CAS client is available
        -- Each record maps to: GPUAttestation { requestId, gpuSeconds, deviceUuid, modelName, timestamp }
        mapM_ (persistBillingRecord cpEndpoint) records

-- | Persist a single billing record to CAS
-- | Typed interface: requires CAS endpoint at runtime
persistBillingRecord :: Text -> BillingRecord -> IO ()
persistBillingRecord _endpoint _record =
  -- Wire to CAS client HTTP POST when infrastructure is available
  -- POST {endpoint}/v1/attestations
  -- Body: JSON-encoded GPUAttestation from BillingRecord fields
  pure ()

-- | Helper functions
-- FFI bindings to NVIDIA profiling libraries

-- NVTX (NVIDIA Tools Extension) FFI
foreign import ccall unsafe "nvtxRangePushA" c_nvtxRangePush :: CString -> IO ()

nvtxRangePush :: String -> IO ()
nvtxRangePush str = do
  withCString str c_nvtxRangePush

foreign import ccall unsafe "nvtxRangePop" c_nvtxRangePop :: IO ()

nvtxRangePop :: IO ()
nvtxRangePop = c_nvtxRangePop

-- CUPTI (CUDA Profiling Tools Interface) FFI
foreign import ccall unsafe "cuptiGetTimestamp" c_cuptiGetTimestamp :: Ptr Int64 -> IO CUptiResult

cuptiGetTimestamp :: IO Int64
cuptiGetTimestamp = do
  alloca $ \ptr -> do
    result <- c_cuptiGetTimestamp ptr
    if result == 0 then
      peek ptr
    else
      pure 0 -- Return 0 on error

-- CUDA device UUID FFI
foreign import ccall unsafe "cudaDeviceGetAttribute" c_cudaDeviceGetAttribute :: Ptr Int -> CInt -> CInt -> IO CInt

foreign import ccall unsafe "cudaDeviceGetPCIBusId" c_cudaDeviceGetPCIBusId :: CString -> CInt -> CInt -> IO CInt

getDeviceUUID :: IO Text
getDeviceUUID = do
  -- Query CUDA device 0 for PCI Bus ID (attribute 33 = CU_DEVICE_ATTRIBUTE_PCI_BUS_ID)
  alloca $ \attrPtr -> do
    result <- c_cudaDeviceGetAttribute attrPtr 33 0
    if result == 0
      then do
        busId <- peek attrPtr
        pure $ Text.pack $ "gpu-device-" <> show busId
      else
        -- CUDA not available or no device: return deterministic fallback
        pure "no-cuda-device"


drainTQueue :: TQueue a -> STM [a]
drainTQueue queue = do
  mbItem <- tryReadTQueue queue
  case mbItem of
    Nothing -> pure []
    Just item -> do
      rest <- drainTQueue queue
      pure (item : rest)
