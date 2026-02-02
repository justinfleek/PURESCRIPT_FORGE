-- | Encoding utilities (base64, hash, checksum)
-- | Migrated from opencode-dev/packages/util/src/encode.ts
module Opencode.Util.Encode
  ( base64Encode
  , base64Decode
  , checksum
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String (length) as String
import Data.String.CodeUnits (charAt, toCharArray)
import Data.Char (toCharCode)
import Data.Array (foldl)
import Data.Int.Bits (xor, shl)

-- | URL-safe base64 encode (FFI required for full implementation)
foreign import base64Encode :: String -> String

-- | URL-safe base64 decode (FFI required for full implementation)
foreign import base64Decode :: String -> String

-- | FNV-1a checksum (pure implementation)
checksum :: String -> Maybe String
checksum content
  | String.length content == 0 = Nothing
  | otherwise = Just (toBase36 (fnv1a content))

-- FNV-1a hash algorithm
fnv1a :: String -> Int
fnv1a content = foldl hashChar 0x811c9dc5 (toCharArray content)
  where
  hashChar :: Int -> Char -> Int
  hashChar hash c =
    let xored = hash `xor` toCharCode c
    in (xored * 0x01000193) `shl` 0

-- Convert to base36 string
foreign import toBase36 :: Int -> String
