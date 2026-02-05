# Accurate Migration Status - Remaining Files

**Last Updated**: 2026-02-04

## Provider Implementations (4 files, ~2,000+ lines) - CRITICAL

These are **CRITICAL** - they contain all the provider-specific transformation logic:

1. **`routes/zen/util/provider/openai.ts`** (631 lines)
   - `openaiHelper` - Provider helper with modifyUrl, modifyHeaders, modifyBody, createBinaryStreamDecoder, streamSeparator, createUsageParser, normalizeUsage
   - `fromOpenaiRequest` - Convert OpenAI format to CommonRequest
   - `toOpenaiRequest` - Convert CommonRequest to OpenAI format
   - `fromOpenaiResponse` - Convert OpenAI response to CommonResponse
   - `toOpenaiResponse` - Convert CommonResponse to OpenAI response
   - `fromOpenaiChunk` - Parse OpenAI streaming chunks
   - `toOpenaiChunk` - Format chunks for OpenAI streaming

2. **`routes/zen/util/provider/anthropic.ts`** (753 lines)
   - `anthropicHelper` - Provider helper (includes Bedrock support, binary stream decoder)
   - `fromAnthropicRequest` - Convert Anthropic format to CommonRequest
   - `toAnthropicRequest` - Convert CommonRequest to Anthropic format
   - `fromAnthropicResponse` - Convert Anthropic response to CommonResponse
   - `toAnthropicResponse` - Convert CommonResponse to Anthropic response
   - `fromAnthropicChunk` - Parse Anthropic streaming chunks
   - `toAnthropicChunk` - Format chunks for Anthropic streaming

3. **`routes/zen/util/provider/google.ts`** (76 lines)
   - `googleHelper` - Provider helper for Google Gemini

4. **`routes/zen/util/provider/openai-compatible.ts`** (547 lines)
   - `oaCompatHelper` - Provider helper for OpenAI-compatible APIs
   - `fromOaCompatibleRequest` - Convert OA-compat format to CommonRequest
   - `toOaCompatibleRequest` - Convert CommonRequest to OA-compat format
   - `fromOaCompatibleResponse` - Convert OA-compat response to CommonResponse
   - `toOaCompatibleResponse` - Convert CommonResponse to OA-compat response
   - `fromOaCompatibleChunk` - Parse OA-compat streaming chunks
   - `toOaCompatibleChunk` - Format chunks for OA-compat streaming

**Current Status**: `Provider.purs` only has types and stubs. The actual provider implementations are **NOT migrated**.

**Impact**: `buildProviderUrl`, `buildProviderBody`, `fetchProviderRequest` in `Handler/Main.purs` are FFI stubs that need these provider helpers to work.

---

## Route Files (3 files)

1. **`routes/temp.tsx`** (173 lines)
   - Home page route with copy-to-clipboard functionality
   - **Status**: NOT migrated

2. **`routes/t/[...path].tsx`** (21 lines)
   - Enterprise proxy route (`/t/*` → `https://enterprise.opencode.ai/*`)
   - **Status**: NOT migrated

3. **`routes/workspace.tsx`** (39 lines)
   - Workspace layout wrapper
   - **Status**: May be covered by `WorkspaceLayout.purs` - needs verification

---

## Other Route Files (3 files)

1. **`routes/temp.tsx`** (173 lines)
   - Home page route with copy-to-clipboard functionality
   - **Status**: NOT migrated

2. **`routes/t/[...path].tsx`** (21 lines)
   - Enterprise proxy route (`/t/*` → `https://enterprise.opencode.ai/*`)
   - **Status**: NOT migrated

3. **`routes/workspace.tsx`** (39 lines)
   - Workspace layout wrapper
   - **Status**: May be covered by `WorkspaceLayout.purs` - needs verification

---

## Summary

**Total Missing**: 7 files minimum
- 4 provider implementation files (~2,000+ lines) - **CRITICAL**
- 3 route files (~233 lines)

**Critical Path**: The provider implementations are essential for the Zen API to function. Without them, `buildProviderUrl`, `buildProviderBody`, and `fetchProviderRequest` cannot work correctly.

**Note**: User mentioned "exec" and "a whole bunch of other stuff" - need to verify if there are additional missing files not yet identified.

---

## Verification Needed

- [ ] Verify `workspace.tsx` is fully covered by `WorkspaceLayout.purs`
- [ ] Check if any other utility files are missing (user mentioned "exec" - need to find)
- [ ] Verify all FFI functions in `Handler/Main.purs` have implementations
- [ ] Check for any other missing route handlers or utilities
- [ ] Verify component files are all migrated
