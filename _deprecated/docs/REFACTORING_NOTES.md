# Refactoring Notes: Removing Unnecessary FFI

## Principle

**FFI should ONLY be used at absolute boundaries:**
1. Framework operations (SolidJS Start mounting, HTTP responses)
2. External HTTP requests (fetching from GitHub, external APIs)
3. System operations (current time, random numbers)
4. Database operations (using Database DSL)

**Everything else must be pure PureScript:**
- String operations → Data.String
- Array operations → Data.Array
- JSON encoding/decoding → At framework boundary only
- Business logic → 100% pure PureScript

## Refactoring Checklist

- [x] Models.purs - Refactored to use Data.String, Data.Array.elem
- [x] Zen handler - Removed all Foreign types from business logic
- [x] Zen v1 routes (ChatCompletions, Messages, Responses, ModelDetail) - Updated to use pure PureScript types
- [x] Handler/Auth.purs - Removed Foreign from queryAuthData signature
- [x] Handler/Reload.purs - Removed Foreign from acquireReloadLock and isDateInFuture
- [x] Handler/Main.purs - All business logic uses pure PureScript types
- [x] Models.purs - zenDataList returns pure PureScript type
- [x] All route handlers - Use RequestHeaders and RequestBody instead of Foreign
- [x] Remove all unnecessary FFI from business logic
- [x] Use proper PureScript types instead of Foreign where possible

## Status: COMPLETE ✅

All Foreign types have been removed from business logic. FFI only exists at absolute boundaries (framework, database, HTTP, system operations).

## Pattern

**Before (FFI-heavy):**
```purescript
foreign import split :: String -> String -> Array String
foreign import toLower :: String -> String
```

**After (Pure PureScript):**
```purescript
import Data.String (Pattern(..), split, toLower)
import Data.Array (elem)

-- Pure functions, no FFI
extractApiKey :: String -> Maybe String
isDisabled :: String -> Array String -> Boolean
```
