{-|
Module      : Tool.ASTEdit.FFI.FileIO
Description : File I/O FFI for AST Edit operations
File I/O operations for reading and writing files in AST Edit context.
-}
module Tool.ASTEdit.FFI.FileIO
  ( readFile
  , writeFile
  , deleteFile
  ) where

import Prelude

import Data.Either (Either)
import Effect.Aff (Aff)

-- | Read file content
foreign import readFile :: String -> Aff (Either String String)

-- | Write file content
foreign import writeFile :: String -> String -> Aff (Either String Unit)

-- | Delete a file
foreign import deleteFile :: String -> Aff (Either String Unit)
