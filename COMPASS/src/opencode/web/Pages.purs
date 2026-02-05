-- | Web Pages - Astro API routes
-- | Phase 5: Desktop/Web Migration
module Opencode.Web.Pages where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as Array
import Data.Either (Either(..))
import Data.String as String
import Tool.ASTEdit.FFI.FileIO (readFile)

-- | API route handler for docs pages
-- | This matches Astro's APIRoute type
type APIRoute =
  { params :: { slug :: Maybe String }
  }

-- | Handle GET request for docs page
handleDocsGET :: APIRoute -> Aff Response
handleDocsGET route = do
  let slug = fromMaybe "index" route.params.slug
  
  -- Get document collection
  docs <- getDocsCollection
  
  -- Find document by slug
  case Array.find (\d -> d.id == slug) docs of
    Nothing -> pure $ createResponse 404 "Not found"
    Just doc -> pure $ createResponse 200 doc.body

-- | Document type
type Document =
  { id :: String
  , body :: String
  }

-- | Get docs collection
-- | Reads documentation files from docs directory
-- | In full Astro integration, this would use Astro's content collection API
getDocsCollection :: Aff (Array Document)
getDocsCollection = do
  -- Try to read docs from common locations
  let docsDirs = 
        [ "docs"
        , "src/docs"
        , "content/docs"
        , "pages/docs"
        ]
  
  -- Try each directory
  results <- Array.traverse (\dir -> readDocsFromDirectory dir) docsDirs
  
  -- Return first non-empty result or empty array
  case Array.find (not <<< Array.null) results of
    Just docs -> pure docs
    Nothing -> pure []
  where
    readDocsFromDirectory :: String -> Aff (Array Document)
    readDocsFromDirectory dir = do
      -- Try to read common doc files
      let docFiles = 
            [ dir <> "/index.md"
            , dir <> "/README.md"
            , dir <> "/getting-started.md"
            , dir <> "/api.md"
            ]
      
      -- Read each file
      fileResults <- Array.traverse (\file -> do
        readResult <- readFile file
        case readResult of
          Left _ -> pure Nothing
          Right content -> do
            let id = extractDocId file
            pure $ Just { id, body: content }
      ) docFiles
      
      pure $ Array.mapMaybe identity fileResults
    
    extractDocId :: String -> String
    extractDocId filePath =
      -- Extract document ID from file path
      -- e.g., "docs/getting-started.md" -> "getting-started"
      let parts = String.split (String.Pattern "/") filePath
          fileName = fromMaybe "" (Array.last parts)
          withoutExt = String.takeWhile (\c -> c /= '.') fileName
      in
        if withoutExt == "" then "index" else withoutExt

-- | Create HTTP response
createResponse :: Int -> String -> Response
createResponse status body =
  { status: status
  , headers: [ { key: "Content-Type", value: "text/plain; charset=utf-8" } ]
  , body: body
  }

-- | Response type
type Response =
  { status :: Int
  , headers :: Array { key :: String, value :: String }
  , body :: String
  }
