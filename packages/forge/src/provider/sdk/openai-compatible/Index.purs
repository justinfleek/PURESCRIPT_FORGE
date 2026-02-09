-- | OpenAI Compatible SDK Index
module Forge.Provider.SDK.OpenAICompatible.Index where

import Forge.Provider.SDK.OpenAICompatible.Provider as Provider

-- Re-export main provider
createOpenAICompatibleProvider :: Provider.OpenAICompatibleProviderConfig -> Provider.OpenAICompatibleProvider
createOpenAICompatibleProvider = Provider.create
