-- | OpenAI Compatible SDK Index
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/index.ts
module Forge.Provider.SDK.OpenAICompatible.Index where

import Forge.Provider.SDK.OpenAICompatible.Provider as Provider

-- Re-export main provider
createOpenAICompatibleProvider :: Provider.OpenAICompatibleProviderConfig -> Provider.OpenAICompatibleProvider
createOpenAICompatibleProvider = Provider.create
