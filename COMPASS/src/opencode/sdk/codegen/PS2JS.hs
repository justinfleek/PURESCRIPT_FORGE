{-# LANGUAGE OverloadedStrings #-}
module PS2JS where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath
import System.Directory

-- | Generate JavaScript/TypeScript from PureScript SDK
generateJS :: FilePath -> FilePath -> IO ()
generateJS psDir jsDir = do
  createDirectoryIfMissing True jsDir
  -- Generate index.ts
  generateIndex jsDir
  -- Generate client.ts
  generateClient jsDir
  -- Generate server.ts
  generateServer jsDir
  putStrLn "Generated JavaScript SDK"

generateIndex :: FilePath -> IO ()
generateIndex dir = do
  let content = T.unlines
        [ "export * from \"./client.js\""
        , "export * from \"./server.js\""
        , ""
        , "import { createOpencodeClient } from \"./client.js\""
        , "import { createOpencodeServer } from \"./server.js\""
        , "import type { ServerOptions } from \"./server.js\""
        , ""
        , "export async function createOpencode(options?: ServerOptions) {"
        , "  const server = await createOpencodeServer({"
        , "    ...options,"
        , "  })"
        , ""
        , "  const client = createOpencodeClient({"
        , "    baseUrl: server.url,"
        , "  })"
        , ""
        , "  return {"
        , "    client,"
        , "    server,"
        , "  }"
        , "}"
        ]
  T.writeFile (dir </> "index.ts") content

generateClient :: FilePath -> IO ()
generateClient dir = do
  let content = T.unlines
        [ "import type { Config } from \"./gen/types.gen.js\""
        , ""
        , "export type OpencodeClientConfig = Config & { directory?: string }"
        , ""
        , "export function createOpencodeClient(config?: OpencodeClientConfig) {"
        , "  // Import generated client from PureScript compilation"
        , "  // PureScript compiles to CommonJS modules in output/"
        , "  const { createOpencodeClient: psCreateClient } = require(\"../output/Opencode.SDK.Client/index.js\")"
        , "  return psCreateClient(config || {})"
        , "}"
        ]
  T.writeFile (dir </> "client.ts") content

generateServer :: FilePath -> IO ()
generateServer dir = do
  let content = T.unlines
        [ "import { spawn } from \"node:child_process\""
        , "import type { Config } from \"./gen/types.gen.js\""
        , ""
        , "export type ServerOptions = {"
        , "  hostname?: string"
        , "  port?: number"
        , "  signal?: AbortSignal"
        , "  timeout?: number"
        , "  config?: Config"
        , "}"
        , ""
        , "export async function createOpencodeServer(options?: ServerOptions) {"
        , "  // Import from PureScript compilation"
        , "  // PureScript compiles to CommonJS modules in output/"
        , "  const { createOpencodeServer: psCreateServer } = require(\"../output/Opencode.SDK.Server/index.js\")"
        , "  return await psCreateServer(options || {})"
        , "}"
        ]
  T.writeFile (dir </> "server.ts") content
