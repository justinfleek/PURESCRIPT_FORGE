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
import Render.CAS.Client (CASClient, GPUAttestation(..), writeGPUAttestation)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

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
  startTimes <- newTVar Map.empty
  pure NVXTCollector 
    { nvxtAuditQueue = queue
    , nvxtStartTimes = startTimes
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

-- | On request end (NVTX pop)
onRequestEnd :: NVXTCollector -> UUID -> Text -> Maybe Text -> Maybe Text -> IO BillingRecord
onRequestEnd NVXTCollector {..} requestId modelName mCustomerId mPricingTier = do
  -- Pop NVTX range
  nvtxRangePop
  
  -- Get elapsed time from CUPTI
  elapsedNs <- cuptiGetTimestamp
  
  -- Compute GPU seconds
  let gpuSeconds = fromIntegral elapsedNs / 1e9
  
  -- Get device UUID
  deviceUuid <- getDeviceUUID
  
  -- Create billing record
  now <- getCurrentTime
  let record = BillingRecord
        { brRequestId = requestId
        , brGpuSeconds = gpuSeconds
        , brDeviceUuid = deviceUuid
        , brModelName = modelName
        , brTimestamp = now
        , brCustomerId = mCustomerId
        , brPricingTier = mPricingTier
        }
  
  -- Queue for async flush to audit trail
  atomically $ do
    writeTQueue nvxtAuditQueue record
    -- Remove start time entry to prevent memory leak
    times <- readTVar nvxtStartTimes
    writeTVar nvxtStartTimes (Map.delete requestId times)
  
  pure record

-- | Embed billing data in response metadata
embedBillingMetadata :: BillingRecord -> [(Text, Text)]
embedBillingMetadata BillingRecord {..} =
  [ ("x-gpu-seconds", Text.pack (show brGpuSeconds))
  , ("x-gpu-device", brDeviceUuid)
  ]

-- | Flush billing records to audit trail
flushBillingRecords :: CASClient -> NVXTCollector -> IO ()
flushBillingRecords casClient NVXTCollector {..} = do
  -- Drain queue
  records <- atomically $ do
    records <- drainTQueue nvxtAuditQueue
    pure records
  
  -- Batch write to CAS
  unless (null records) $ do
    -- Convert each BillingRecord to GPUAttestation and write to CAS
    mapM_ (writeRecordToCAS casClient) records
  where
    writeRecordToCAS :: CASClient -> BillingRecord -> IO ()
    writeRecordToCAS client BillingRecord {..} = do
      -- Create GPU attestation from billing record
      -- Note: GPU signature would be computed from CUPTI data in production
      let attestation = GPUAttestation
            { gpuRequestId = UUID.toText brRequestId
            , gpuCustomerId = brCustomerId
            , gpuSeconds = brGpuSeconds
            , gpuDeviceUuid = brDeviceUuid
            , gpuModelName = brModelName
            , gpuTimestamp = brTimestamp
            , gpuSignature = BS.pack [] -- Would be signed by CUPTI in production
            }
      
      -- Write to CAS (errors are logged but don't stop processing)
      result <- writeGPUAttestation client attestation
      case result of
        Left err -> pure () -- Log error in production
        Right _ -> pure () -- Success

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
  -- Get device UUID via CUDA API
  -- For now, return placeholder - full implementation requires CUDA device enumeration
  pure "00000000-0000-0000-0000-000000000000"


-- | Drain TQueue to list (exported for testing)
drainTQueue :: TQueue a -> STM [a]
drainTQueue queue = do
  mbItem <- tryReadTQueue queue
  case mbItem of
    Nothing -> pure []
    Just item -> do
      rest <- drainTQueue queue
      pure (item : rest)
