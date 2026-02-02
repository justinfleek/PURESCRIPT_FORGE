-- | OpenAI Compatible SDK Index
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/index.ts
module Opencode.Provider.SDK.OpenAICompatible.Index where

import Opencode.Provider.SDK.OpenAICompatible.Provider as Provider

-- Re-export main provider
createOpenAICompatibleProvider :: Provider.OpenAICompatibleProviderConfig -> Provider.OpenAICompatibleProvider
createOpenAICompatibleProvider = Provider.create
