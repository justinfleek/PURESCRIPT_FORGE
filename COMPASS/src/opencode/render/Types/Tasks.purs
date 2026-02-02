-- | Render Tasks
-- |
-- | Generation task definitions and input requirements.
-- |
-- | Coeffect Equation:
-- |   Task : Modality -> InputRequirements -> OutputType
-- |   TaskRequirements : Task -> {prompt, image, video, mask}
-- |
-- | Module Coverage: Task enum, task requirements
module Render.Types.Tasks
  ( -- * Tasks
    Task(..)
  , allTasks
    -- * Requirements
  , TaskRequirements
  , taskRequirements
  ) where

import Prelude
import Data.Generic.Rep (class Generic)

--------------------------------------------------------------------------------
-- | Tasks
--------------------------------------------------------------------------------

-- | Generation tasks
data Task
  -- Image tasks
  = T2I           -- text-to-image
  | I2I           -- image-to-image (style transfer)
  | Edit          -- inpaint/outpaint with mask
  | Upscale       -- image upscaling
  -- Video tasks
  | T2V           -- text-to-video
  | I2V           -- image-to-video (animate still)
  | V2V           -- video-to-video (transform/restyle)
  | VideoUpscale  -- video upscaling
  -- 3D tasks
  | I23D          -- image-to-3D
  | T23D          -- text-to-3D
  | V23D          -- video-to-3D
  -- LLM tasks
  | Completion    -- text completion
  | Chat          -- chat/instruct
  | Embed         -- embedding generation
  -- Vision tasks
  | VQA           -- visual question answering
  | Caption       -- image captioning

derive instance eqTask :: Eq Task
derive instance ordTask :: Ord Task
derive instance genericTask :: Generic Task _

instance showTask :: Show Task where
  show = case _ of
    T2I -> "t2i"
    I2I -> "i2i"
    Edit -> "edit"
    Upscale -> "upscale"
    T2V -> "t2v"
    I2V -> "i2v"
    V2V -> "v2v"
    VideoUpscale -> "video-upscale"
    I23D -> "i23d"
    T23D -> "t23d"
    V23D -> "v23d"
    Completion -> "completion"
    Chat -> "chat"
    Embed -> "embed"
    VQA -> "vqa"
    Caption -> "caption"

allTasks :: Array Task
allTasks = [T2I, I2I, Edit, Upscale, T2V, I2V, V2V, VideoUpscale, I23D, T23D, V23D, Completion, Chat, Embed, VQA, Caption]

--------------------------------------------------------------------------------
-- | Task Requirements
--------------------------------------------------------------------------------

-- | What inputs does a task require?
type TaskRequirements =
  { prompt :: Boolean
  , image :: Boolean
  , video :: Boolean
  , mask :: Boolean
  }

taskRequirements :: Task -> TaskRequirements
taskRequirements = case _ of
  T2I -> { prompt: true, image: false, video: false, mask: false }
  I2I -> { prompt: true, image: true, video: false, mask: false }
  Edit -> { prompt: true, image: true, video: false, mask: true }
  Upscale -> { prompt: false, image: true, video: false, mask: false }
  T2V -> { prompt: true, image: false, video: false, mask: false }
  I2V -> { prompt: true, image: true, video: false, mask: false }
  V2V -> { prompt: true, image: false, video: true, mask: false }
  VideoUpscale -> { prompt: false, image: false, video: true, mask: false }
  I23D -> { prompt: false, image: true, video: false, mask: false }
  T23D -> { prompt: true, image: false, video: false, mask: false }
  V23D -> { prompt: false, image: false, video: true, mask: false }
  Completion -> { prompt: true, image: false, video: false, mask: false }
  Chat -> { prompt: true, image: false, video: false, mask: false }
  Embed -> { prompt: true, image: false, video: false, mask: false }
  VQA -> { prompt: true, image: true, video: false, mask: false }
  Caption -> { prompt: false, image: true, video: false, mask: false }
