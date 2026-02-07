module Forge.Enterprise.Types where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?), (:=), (:=?))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | Task type
data TaskId = T2V | I2V | T2I | I2I | Edit

derive instance eqTaskId :: Eq TaskId
derive instance ordTaskId :: Ord TaskId

instance showTaskId :: Show TaskId where
  show T2V = "t2v"
  show I2V = "i2v"
  show T2I = "t2i"
  show I2I = "i2i"
  show Edit = "edit"

instance encodeJsonTaskId :: EncodeJson TaskId where
  encodeJson = encodeJson <<< show

instance decodeJsonTaskId :: DecodeJson TaskId where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "t2v" -> pure T2V
      "i2v" -> pure I2V
      "t2i" -> pure T2I
      "i2i" -> pure I2I
      "edit" -> pure Edit
      _ -> Left "Invalid task ID"

-- | Video format
data VideoFormatId = Video720P | Video720PPortrait | Video480P | Video480PPortrait | VideoSquare

derive instance eqVideoFormatId :: Eq VideoFormatId
derive instance ordVideoFormatId :: Ord VideoFormatId

instance showVideoFormatId :: Show VideoFormatId where
  show Video720P = "720p"
  show Video720PPortrait = "720p-portrait"
  show Video480P = "480p"
  show Video480PPortrait = "480p-portrait"
  show VideoSquare = "square"

instance encodeJsonVideoFormatId :: EncodeJson VideoFormatId where
  encodeJson = encodeJson <<< show

instance decodeJsonVideoFormatId :: DecodeJson VideoFormatId where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "720p" -> pure Video720P
      "720p-portrait" -> pure Video720PPortrait
      "480p" -> pure Video480P
      "480p-portrait" -> pure Video480PPortrait
      "square" -> pure VideoSquare
      _ -> Left "Invalid video format"

-- | Image format
data ImageFormatId = Image1024 | Image512 | ImagePortrait | ImagePortraitWide | ImageLandscape | ImageLandscapeWide

derive instance eqImageFormatId :: Eq ImageFormatId
derive instance ordImageFormatId :: Ord ImageFormatId

instance showImageFormatId :: Show ImageFormatId where
  show Image1024 = "1024"
  show Image512 = "512"
  show ImagePortrait = "portrait"
  show ImagePortraitWide = "portrait-wide"
  show ImageLandscape = "landscape"
  show ImageLandscapeWide = "landscape-wide"

instance encodeJsonImageFormatId :: EncodeJson ImageFormatId where
  encodeJson = encodeJson <<< show

instance decodeJsonImageFormatId :: DecodeJson ImageFormatId where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "1024" -> pure Image1024
      "512" -> pure Image512
      "portrait" -> pure ImagePortrait
      "portrait-wide" -> pure ImagePortraitWide
      "landscape" -> pure ImageLandscape
      "landscape-wide" -> pure ImageLandscapeWide
      _ -> Left "Invalid image format"

-- | Backend
data BackendId = Nunchaku | Torch | TensorRT

derive instance eqBackendId :: Eq BackendId
derive instance ordBackendId :: Ord BackendId

instance showBackendId :: Show BackendId where
  show Nunchaku = "nunchaku"
  show Torch = "torch"
  show TensorRT = "tensorrt"

instance encodeJsonBackendId :: EncodeJson BackendId where
  encodeJson = encodeJson <<< show

instance decodeJsonBackendId :: DecodeJson BackendId where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "nunchaku" -> pure Nunchaku
      "torch" -> pure Torch
      "tensorrt" -> pure TensorRT
      _ -> Left "Invalid backend ID"

-- | Job status
data JobStatus = Queued | Running | Complete | Error | Cancelled

derive instance eqJobStatus :: Eq JobStatus
derive instance ordJobStatus :: Ord JobStatus

instance showJobStatus :: Show JobStatus where
  show Queued = "queued"
  show Running = "running"
  show Complete = "complete"
  show Error = "error"
  show Cancelled = "cancelled"

instance encodeJsonJobStatus :: EncodeJson JobStatus where
  encodeJson = encodeJson <<< show

instance decodeJsonJobStatus :: DecodeJson JobStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "queued" -> pure Queued
      "running" -> pure Running
      "complete" -> pure Complete
      "error" -> pure Error
      "cancelled" -> pure Cancelled
      _ -> Left "Invalid job status"

-- | Job ID (pattern: ^j_[a-zA-Z0-9]{12,}$)
type JobId = String

-- | Asset ID (pattern: ^a_[a-zA-Z0-9]{12,}$)
type AssetId = String

-- | Request ID (pattern: ^req_[a-zA-Z0-9]+$)
type RequestId = String

-- | Prompt (1-4000 chars)
type Prompt = String

-- | Negative prompt (max 2000 chars)
type NegativePrompt = String

-- | Image reference (HTTPS URL, asset URL, or base64 data URI)
type ImageRef = String

-- | Seed (0-4294967295)
type Seed = Int

-- | Progress (0.0 to 1.0)
type Progress = Number

-- | Video generation request
type VideoGenerateRequest =
  { prompt :: Prompt
  , image :: Maybe ImageRef
  , negativePrompt :: Maybe NegativePrompt
  , duration :: Maybe Number
  , steps :: Maybe Int
  , cfg :: Maybe Number
  , seed :: Maybe Seed
  , sampler :: Maybe String
  , scheduler :: Maybe String
  , shift :: Maybe Number
  , motionStrength :: Maybe Number
  , lightning :: Maybe Boolean
  }

instance encodeJsonVideoGenerateRequest :: EncodeJson VideoGenerateRequest where
  encodeJson r = encodeJson
    { prompt: r.prompt
    , image: r.image
    , negative_prompt: r.negativePrompt
    , duration: r.duration
    , steps: r.steps
    , cfg: r.cfg
    , seed: r.seed
    , sampler: r.sampler
    , scheduler: r.scheduler
    , shift: r.shift
    , motion_strength: r.motionStrength
    , lightning: r.lightning
    }

instance decodeJsonVideoGenerateRequest :: DecodeJson VideoGenerateRequest where
  decodeJson json = do
    obj <- decodeJson json
    prompt <- obj .: "prompt"
    image <- obj .:? "image"
    negativePrompt <- obj .:? "negative_prompt"
    duration <- obj .:? "duration"
    steps <- obj .:? "steps"
    cfg <- obj .:? "cfg"
    seed <- obj .:? "seed"
    sampler <- obj .:? "sampler"
    scheduler <- obj .:? "scheduler"
    shift <- obj .:? "shift"
    motionStrength <- obj .:? "motion_strength"
    lightning <- obj .:? "lightning"
    pure { prompt, image, negativePrompt, duration, steps, cfg, seed, sampler, scheduler, shift, motionStrength, lightning }

-- | Image generation request
type ImageGenerateRequest =
  { prompt :: Prompt
  , image :: Maybe ImageRef
  , mask :: Maybe ImageRef
  , negativePrompt :: Maybe NegativePrompt
  , strength :: Maybe Number
  , steps :: Maybe Int
  , guidance :: Maybe Number
  , cfg :: Maybe Number
  , count :: Maybe Int
  , seed :: Maybe Seed
  , sampler :: Maybe String
  , scheduler :: Maybe String
  , noiseType :: Maybe String
  , eta :: Maybe Number
  , clipSkip :: Maybe Int
  , lora :: Maybe (Array { id :: String, weight :: Number })
  , detailAmount :: Maybe Number
  , detailStart :: Maybe Number
  , detailEnd :: Maybe Number
  }

instance encodeJsonImageGenerateRequest :: EncodeJson ImageGenerateRequest where
  encodeJson r = encodeJson
    { prompt: r.prompt
    , image: r.image
    , mask: r.mask
    , negative_prompt: r.negativePrompt
    , strength: r.strength
    , steps: r.steps
    , guidance: r.guidance
    , cfg: r.cfg
    , count: r.count
    , seed: r.seed
    , sampler: r.sampler
    , scheduler: r.scheduler
    , noise_type: r.noiseType
    , eta: r.eta
    , clip_skip: r.clipSkip
    , lora: r.lora
    , detail_amount: r.detailAmount
    , detail_start: r.detailStart
    , detail_end: r.detailEnd
    }

instance decodeJsonImageGenerateRequest :: DecodeJson ImageGenerateRequest where
  decodeJson json = do
    obj <- decodeJson json
    prompt <- obj .: "prompt"
    image <- obj .:? "image"
    mask <- obj .:? "mask"
    negativePrompt <- obj .:? "negative_prompt"
    strength <- obj .:? "strength"
    steps <- obj .:? "steps"
    guidance <- obj .:? "guidance"
    cfg <- obj .:? "cfg"
    count <- obj .:? "count"
    seed <- obj .:? "seed"
    sampler <- obj .:? "sampler"
    scheduler <- obj .:? "scheduler"
    noiseType <- obj .:? "noise_type"
    eta <- obj .:? "eta"
    clipSkip <- obj .:? "clip_skip"
    lora <- obj .:? "lora"
    detailAmount <- obj .:? "detail_amount"
    detailStart <- obj .:? "detail_start"
    detailEnd <- obj .:? "detail_end"
    pure { prompt, image, mask, negativePrompt, strength, steps, guidance, cfg, count, seed, sampler, scheduler, noiseType, eta, clipSkip, lora, detailAmount, detailStart, detailEnd }

-- | Job
type Job =
  { id :: JobId
  , status :: JobStatus
  , position :: Maybe Int
  , progress :: Maybe Progress
  , etaSeconds :: Maybe Int
  , output :: Maybe String
  , outputs :: Maybe (Array String)
  , seed :: Maybe Seed
  , error :: Maybe { code :: String, message :: String, retriable :: Boolean }
  , createdAt :: String
  , startedAt :: Maybe String
  , completedAt :: Maybe String
  , request :: Maybe Json
  }

instance encodeJsonJob :: EncodeJson Job where
  encodeJson j = encodeJson
    { id: j.id
    , status: j.status
    , position: j.position
    , progress: j.progress
    , eta_seconds: j.etaSeconds
    , output: j.output
    , outputs: j.outputs
    , seed: j.seed
    , error: j.error
    , created_at: j.createdAt
    , started_at: j.startedAt
    , completed_at: j.completedAt
    , request: j.request
    }

instance decodeJsonJob :: DecodeJson Job where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    status <- obj .: "status"
    position <- obj .:? "position"
    progress <- obj .:? "progress"
    etaSeconds <- obj .:? "eta_seconds"
    output <- obj .:? "output"
    outputs <- obj .:? "outputs"
    seed <- obj .:? "seed"
    error <- obj .:? "error"
    createdAt <- obj .: "created_at"
    startedAt <- obj .:? "started_at"
    completedAt <- obj .:? "completed_at"
    request <- obj .:? "request"
    pure { id, status, position, progress, etaSeconds, output, outputs, seed, error, createdAt, startedAt, completedAt, request }

-- | Job created response
type JobCreated =
  { id :: JobId
  , status :: JobStatus
  , position :: Int
  , etaSeconds :: Maybe Int
  , eventsUrl :: Maybe String
  }

instance encodeJsonJobCreated :: EncodeJson JobCreated where
  encodeJson j = encodeJson
    { id: j.id
    , status: j.status
    , position: j.position
    , eta_seconds: j.etaSeconds
    , events_url: j.eventsUrl
    }

instance decodeJsonJobCreated :: DecodeJson JobCreated where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    status <- obj .: "status"
    position <- obj .: "position"
    etaSeconds <- obj .:? "eta_seconds"
    eventsUrl <- obj .:? "events_url"
    pure { id, status, position, etaSeconds, eventsUrl }

-- | Async job request
type AsyncJobRequest =
  { modality :: String
  , family :: String
  , model :: String
  , task :: TaskId
  , format :: Maybe String
  , backend :: Maybe BackendId
  , prompt :: Prompt
  , image :: Maybe ImageRef
  , mask :: Maybe ImageRef
  , negativePrompt :: Maybe NegativePrompt
  , seed :: Maybe Seed
  , duration :: Maybe Number
  , steps :: Maybe Int
  , guidance :: Maybe Number
  , strength :: Maybe Number
  , count :: Maybe Int
  , priority :: Maybe String
  , webhook :: Maybe String
  , ttl :: Maybe Int
  , idempotencyKey :: Maybe String
  }

instance encodeJsonAsyncJobRequest :: EncodeJson AsyncJobRequest where
  encodeJson r = encodeJson
    { modality: r.modality
    , family: r.family
    , model: r.model
    , task: r.task
    , format: r.format
    , backend: r.backend
    , prompt: r.prompt
    , image: r.image
    , mask: r.mask
    , negative_prompt: r.negativePrompt
    , seed: r.seed
    , duration: r.duration
    , steps: r.steps
    , guidance: r.guidance
    , strength: r.strength
    , count: r.count
    , priority: r.priority
    , webhook: r.webhook
    , ttl: r.ttl
    , idempotency_key: r.idempotencyKey
    }

instance decodeJsonAsyncJobRequest :: DecodeJson AsyncJobRequest where
  decodeJson json = do
    obj <- decodeJson json
    modality <- obj .: "modality"
    family <- obj .: "family"
    model <- obj .: "model"
    task <- obj .: "task"
    format <- obj .:? "format"
    backend <- obj .:? "backend"
    prompt <- obj .: "prompt"
    image <- obj .:? "image"
    mask <- obj .:? "mask"
    negativePrompt <- obj .:? "negative_prompt"
    seed <- obj .:? "seed"
    duration <- obj .:? "duration"
    steps <- obj .:? "steps"
    guidance <- obj .:? "guidance"
    strength <- obj .:? "strength"
    count <- obj .:? "count"
    priority <- obj .:? "priority"
    webhook <- obj .:? "webhook"
    ttl <- obj .:? "ttl"
    idempotencyKey <- obj .:? "idempotency_key"
    pure { modality, family, model, task, format, backend, prompt, image, mask, negativePrompt, seed, duration, steps, guidance, strength, count, priority, webhook, ttl, idempotencyKey }

-- | Model status
data ModelStatus = Active | Preview | ComingSoon | Deprecated

derive instance eqModelStatus :: Eq ModelStatus
derive instance ordModelStatus :: Ord ModelStatus

instance showModelStatus :: Show ModelStatus where
  show Active = "active"
  show Preview = "preview"
  show ComingSoon = "coming_soon"
  show Deprecated = "deprecated"

instance encodeJsonModelStatus :: EncodeJson ModelStatus where
  encodeJson = encodeJson <<< show

instance decodeJsonModelStatus :: DecodeJson ModelStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "active" -> pure Active
      "preview" -> pure Preview
      "coming_soon" -> pure ComingSoon
      "deprecated" -> pure Deprecated
      _ -> Left "Invalid model status"

-- | Model preset
type ModelPreset =
  { sampler :: Maybe String
  , scheduler :: Maybe String
  , steps :: Maybe Int
  , cfg :: Maybe Number
  , guidance :: Maybe Number
  , notes :: Maybe String
  }

instance encodeJsonModelPreset :: EncodeJson ModelPreset where
  encodeJson p = encodeJson
    { sampler: p.sampler
    , scheduler: p.scheduler
    , steps: p.steps
    , cfg: p.cfg
    , guidance: p.guidance
    , notes: p.notes
    }

instance decodeJsonModelPreset :: DecodeJson ModelPreset where
  decodeJson json = do
    obj <- decodeJson json
    sampler <- obj .:? "sampler"
    scheduler <- obj .:? "scheduler"
    steps <- obj .:? "steps"
    cfg <- obj .:? "cfg"
    guidance <- obj .:? "guidance"
    notes <- obj .:? "notes"
    pure { sampler, scheduler, steps, cfg, guidance, notes }

-- | Model capability
type ModelCapability =
  { family :: String
  , model :: String
  , modality :: String
  , tasks :: Array TaskId
  , formats :: Array String
  , backends :: Array BackendId
  , defaultBackend :: Maybe BackendId
  , status :: ModelStatus
  , aliases :: Maybe (Array String)
  , presets :: Maybe { fast :: Maybe ModelPreset, standard :: Maybe ModelPreset, quality :: Maybe ModelPreset }
  , notes :: Maybe String
  }

instance encodeJsonModelCapability :: EncodeJson ModelCapability where
  encodeJson c = encodeJson
    { family: c.family
    , model: c.model
    , modality: c.modality
    , tasks: c.tasks
    , formats: c.formats
    , backends: c.backends
    , default_backend: c.defaultBackend
    , status: c.status
    , aliases: c.aliases
    , presets: c.presets
    , notes: c.notes
    }

instance decodeJsonModelCapability :: DecodeJson ModelCapability where
  decodeJson json = do
    obj <- decodeJson json
    family <- obj .: "family"
    model <- obj .: "model"
    modality <- obj .: "modality"
    tasks <- obj .: "tasks"
    formats <- obj .: "formats"
    backends <- obj .: "backends"
    defaultBackend <- obj .:? "default_backend"
    status <- obj .: "status"
    aliases <- obj .:? "aliases"
    presets <- obj .:? "presets"
    notes <- obj .:? "notes"
    pure { family, model, modality, tasks, formats, backends, defaultBackend, status, aliases, presets, notes }

-- | Models response
type ModelsResponse =
  { video :: Array ModelCapability
  , image :: Array ModelCapability
  }

instance encodeJsonModelsResponse :: EncodeJson ModelsResponse where
  encodeJson r = encodeJson
    { video: r.video
    , image: r.image
    }

instance decodeJsonModelsResponse :: DecodeJson ModelsResponse where
  decodeJson json = do
    obj <- decodeJson json
    video <- obj .: "video"
    image <- obj .: "image"
    pure { video, image }

-- | Create upload request
type CreateUploadRequest =
  { contentType :: String
  , bytes :: Int
  }

instance encodeJsonCreateUploadRequest :: EncodeJson CreateUploadRequest where
  encodeJson r = encodeJson
    { content_type: r.contentType
    , bytes: r.bytes
    }

instance decodeJsonCreateUploadRequest :: DecodeJson CreateUploadRequest where
  decodeJson json = do
    obj <- decodeJson json
    contentType <- obj .: "content_type"
    bytes <- obj .: "bytes"
    pure { contentType, bytes }

-- | Create upload response
type CreateUploadResponse =
  { uploadUrl :: String
  , assetUrl :: String
  }

instance encodeJsonCreateUploadResponse :: EncodeJson CreateUploadResponse where
  encodeJson r = encodeJson
    { upload_url: r.uploadUrl
    , asset_url: r.assetUrl
    }

instance decodeJsonCreateUploadResponse :: DecodeJson CreateUploadResponse where
  decodeJson json = do
    obj <- decodeJson json
    uploadUrl <- obj .: "upload_url"
    assetUrl <- obj .: "asset_url"
    pure { uploadUrl, assetUrl }

-- | Error response
type ErrorResponse =
  { error :: String
  , message :: String
  , requestId :: Maybe RequestId
  , details :: Maybe Json
  }

instance encodeJsonErrorResponse :: EncodeJson ErrorResponse where
  encodeJson e = encodeJson
    { error: e.error
    , message: e.message
    , request_id: e.requestId
    , details: e.details
    }

instance decodeJsonErrorResponse :: DecodeJson ErrorResponse where
  decodeJson json = do
    obj <- decodeJson json
    error <- obj .: "error"
    message <- obj .: "message"
    requestId <- obj .:? "request_id"
    details <- obj .:? "details"
    pure { error, message, requestId, details }
