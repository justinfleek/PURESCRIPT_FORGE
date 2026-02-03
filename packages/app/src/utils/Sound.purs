-- | Sound playback utilities
-- | Migrated from: forge-dev/packages/app/src/utils/sound.ts (118 lines)
module Sidepanel.Utils.Sound
  ( SoundOption
  , SoundID
  , soundOptions
  , soundSrc
  , playSound
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)

-- | Sound option record
type SoundOption =
  { id :: String
  , label :: String
  , src :: String
  }

-- | Sound ID type alias
type SoundID = String

-- | All available sound options
soundOptions :: Array SoundOption
soundOptions =
  -- Alert sounds
  [ { id: "alert-01", label: "sound.option.alert01", src: alertSrc 1 }
  , { id: "alert-02", label: "sound.option.alert02", src: alertSrc 2 }
  , { id: "alert-03", label: "sound.option.alert03", src: alertSrc 3 }
  , { id: "alert-04", label: "sound.option.alert04", src: alertSrc 4 }
  , { id: "alert-05", label: "sound.option.alert05", src: alertSrc 5 }
  , { id: "alert-06", label: "sound.option.alert06", src: alertSrc 6 }
  , { id: "alert-07", label: "sound.option.alert07", src: alertSrc 7 }
  , { id: "alert-08", label: "sound.option.alert08", src: alertSrc 8 }
  , { id: "alert-09", label: "sound.option.alert09", src: alertSrc 9 }
  , { id: "alert-10", label: "sound.option.alert10", src: alertSrc 10 }
  -- Bip-bop sounds
  , { id: "bip-bop-01", label: "sound.option.bipbop01", src: bipBopSrc 1 }
  , { id: "bip-bop-02", label: "sound.option.bipbop02", src: bipBopSrc 2 }
  , { id: "bip-bop-03", label: "sound.option.bipbop03", src: bipBopSrc 3 }
  , { id: "bip-bop-04", label: "sound.option.bipbop04", src: bipBopSrc 4 }
  , { id: "bip-bop-05", label: "sound.option.bipbop05", src: bipBopSrc 5 }
  , { id: "bip-bop-06", label: "sound.option.bipbop06", src: bipBopSrc 6 }
  , { id: "bip-bop-07", label: "sound.option.bipbop07", src: bipBopSrc 7 }
  , { id: "bip-bop-08", label: "sound.option.bipbop08", src: bipBopSrc 8 }
  , { id: "bip-bop-09", label: "sound.option.bipbop09", src: bipBopSrc 9 }
  , { id: "bip-bop-10", label: "sound.option.bipbop10", src: bipBopSrc 10 }
  -- Staplebops sounds
  , { id: "staplebops-01", label: "sound.option.staplebops01", src: staplebopsSrc 1 }
  , { id: "staplebops-02", label: "sound.option.staplebops02", src: staplebopsSrc 2 }
  , { id: "staplebops-03", label: "sound.option.staplebops03", src: staplebopsSrc 3 }
  , { id: "staplebops-04", label: "sound.option.staplebops04", src: staplebopsSrc 4 }
  , { id: "staplebops-05", label: "sound.option.staplebops05", src: staplebopsSrc 5 }
  , { id: "staplebops-06", label: "sound.option.staplebops06", src: staplebopsSrc 6 }
  , { id: "staplebops-07", label: "sound.option.staplebops07", src: staplebopsSrc 7 }
  -- Nope sounds
  , { id: "nope-01", label: "sound.option.nope01", src: nopeSrc 1 }
  , { id: "nope-02", label: "sound.option.nope02", src: nopeSrc 2 }
  , { id: "nope-03", label: "sound.option.nope03", src: nopeSrc 3 }
  , { id: "nope-04", label: "sound.option.nope04", src: nopeSrc 4 }
  , { id: "nope-05", label: "sound.option.nope05", src: nopeSrc 5 }
  , { id: "nope-06", label: "sound.option.nope06", src: nopeSrc 6 }
  , { id: "nope-07", label: "sound.option.nope07", src: nopeSrc 7 }
  , { id: "nope-08", label: "sound.option.nope08", src: nopeSrc 8 }
  , { id: "nope-09", label: "sound.option.nope09", src: nopeSrc 9 }
  , { id: "nope-10", label: "sound.option.nope10", src: nopeSrc 10 }
  , { id: "nope-11", label: "sound.option.nope11", src: nopeSrc 11 }
  , { id: "nope-12", label: "sound.option.nope12", src: nopeSrc 12 }
  -- Yup sounds
  , { id: "yup-01", label: "sound.option.yup01", src: yupSrc 1 }
  , { id: "yup-02", label: "sound.option.yup02", src: yupSrc 2 }
  , { id: "yup-03", label: "sound.option.yup03", src: yupSrc 3 }
  , { id: "yup-04", label: "sound.option.yup04", src: yupSrc 4 }
  , { id: "yup-05", label: "sound.option.yup05", src: yupSrc 5 }
  , { id: "yup-06", label: "sound.option.yup06", src: yupSrc 6 }
  ]

-- | Sound source URL generators
foreign import alertSrc :: Int -> String
foreign import bipBopSrc :: Int -> String
foreign import staplebopsSrc :: Int -> String
foreign import nopeSrc :: Int -> String
foreign import yupSrc :: Int -> String

-- | Map of sound ID to source URL
soundById :: Map String String
soundById = Map.fromFoldable $ map (\opt -> Tuple opt.id opt.src) soundOptions

-- | Get sound source URL by ID
-- | Returns Nothing if ID is invalid
soundSrc :: Maybe String -> Maybe String
soundSrc maybeId = case maybeId of
  Nothing -> Nothing
  Just id -> Map.lookup id soundById

-- | Play a sound from URL
-- | Returns cleanup function to stop playback
-- | Returns Nothing if Audio is not available
playSound :: Maybe String -> Effect (Maybe (Effect Unit))
playSound maybeSrc = case maybeSrc of
  Nothing -> pure Nothing
  Just src -> do
    hasAudio <- hasAudioSupport
    if hasAudio
    then do
      audio <- createAudio src
      playAudio audio
      pure $ Just $ stopAudio audio
    else
      pure Nothing

-- | Check if Audio API is available
foreign import hasAudioSupport :: Effect Boolean

-- | Create Audio element
foreign import createAudio :: String -> Effect AudioElement

-- | Play Audio element
foreign import playAudio :: AudioElement -> Effect Unit

-- | Stop and reset Audio element
foreign import stopAudio :: AudioElement -> Effect Unit

-- | Audio element type (opaque)
foreign import data AudioElement :: Type
