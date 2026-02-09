{-# LANGUAGE OverloadedStrings #-}
-- Phase 7: Hot Reload Support
module HotReload where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified System.FilePath as FP
import qualified System.Directory as Dir
import qualified Data.Map.Strict as Map
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as BS
import Parser (PSModule(..), parseModule)
import TypeChecker (typeCheckModule)
import Cpp23Generator (generateCpp23Header, generateCpp23Impl, toCppHeaderName)

-- | Hot reload manager
data HotReloadManager = HotReloadManager
  { watchedFiles :: Map.Map FilePath FileHash
  , reloadCallbacks :: [FilePath -> IO ()]
  , outputDirectory :: FilePath
  }

-- | File hash for change detection
type FileHash = T.Text

-- | Initialize hot reload manager
initHotReload :: FilePath -> IO HotReloadManager
initHotReload outputDir = do
  Dir.createDirectoryIfMissing True outputDir
  return HotReloadManager
    { watchedFiles = Map.empty
    , reloadCallbacks = []
    , outputDirectory = outputDir
    }

-- | Watch file for changes
watchFile :: HotReloadManager -> FilePath -> IO HotReloadManager
watchFile manager filePath = do
  hash <- computeFileHash filePath
  let updated = Map.insert filePath hash (watchedFiles manager)
  return manager { watchedFiles = updated }

-- | Check for file changes and reload if needed
checkAndReload :: HotReloadManager -> FilePath -> IO (Maybe HotReloadManager)
checkAndReload manager filePath = do
  exists <- Dir.doesFileExist filePath
  if not exists
    then return Nothing
    else do
      currentHash <- computeFileHash filePath
      let oldHash = Map.lookup filePath (watchedFiles manager)
      
      if oldHash /= Just currentHash
        then do
          -- File changed, reload
          reloadFile manager filePath
          let updated = Map.insert filePath currentHash (watchedFiles manager)
          return $ Just manager { watchedFiles = updated }
        else
          return Nothing

-- | Reload file and regenerate code
reloadFile :: HotReloadManager -> FilePath -> IO ()
reloadFile manager filePath = do
  content <- TIO.readFile filePath
  case parseModule content of
    Left parseErr -> do
      putStrLn $ "Parse error in " ++ filePath ++ ": " ++ show parseErr
      return ()
    Right module' -> do
      case typeCheckModule module' of
        Left typeErr -> do
          putStrLn $ "Type error in " ++ filePath ++ ": " ++ T.unpack typeErr
          return ()
        Right checkedModule -> do
          -- Generate C++23 code
          let header = generateCpp23Header checkedModule
          let impl = generateCpp23Impl checkedModule
          let headerName = outputDirectory manager ++ "/" ++ T.unpack (toCppHeaderName (moduleName checkedModule)) ++ ".hpp"
          let implName = outputDirectory manager ++ "/" ++ T.unpack (toCppHeaderName (moduleName checkedModule)) ++ ".cpp"
          
          TIO.writeFile headerName header
          TIO.writeFile implName impl
          
          putStrLn $ "Reloaded: " ++ filePath
          putStrLn $ "  Generated: " ++ headerName
          putStrLn $ "  Generated: " ++ implName
          
          -- Notify callbacks
          mapM_ (\callback -> callback filePath) (reloadCallbacks manager)

-- | Compute file hash using SHA256
computeFileHash :: FilePath -> IO FileHash
computeFileHash filePath = do
  content <- BS.readFile filePath
  let hash = SHA256.hash content
  return $ T.pack (show hash)

-- | Register reload callback
registerCallback :: HotReloadManager -> (FilePath -> IO ()) -> HotReloadManager
registerCallback manager callback =
  manager { reloadCallbacks = callback : reloadCallbacks manager }

-- | Watch multiple files
watchFiles :: HotReloadManager -> [FilePath] -> IO HotReloadManager
watchFiles manager files = do
  foldM watchFile manager files
