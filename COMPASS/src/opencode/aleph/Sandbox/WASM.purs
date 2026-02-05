{-|
Module      : Aleph.Sandbox.WASM
Description : WebAssembly sandboxing for untrusted code execution
|= WASM Sandbox

This module provides secure WebAssembly sandboxing for executing untrusted
code. WASM provides strong isolation guarantees through its capability-based
security model and linear memory.

== Security Model

WASM sandboxing provides:
- **Memory isolation**: Linear memory is isolated from host
- **Capability-based**: Only explicitly granted capabilities are available
- **Deterministic execution**: Same input → same output
- **Resource limits**: CPU time, memory, and instruction limits
- **No host access**: Cannot access filesystem, network, or system calls without explicit imports

== WASM Runtime

Uses wasmtime for secure execution:
- Validates WASM modules before execution
- Enforces resource limits
- Provides capability-based host function imports
- Supports WASI for controlled system access

== Coeffect Equation

@
  wasmSandbox : WASMConfig -> Graded WASM (WASMResult a)

  -- Requires:
  -- 1. WASM runtime resource
  -- 2. Memory allocation for WASM linear memory
  -- 3. CPU time quota
@
-}
module Aleph.Sandbox.WASM
  ( -- * Configuration
    WASMConfig(..)
  , WASMMemoryLimit(..)
  , WASMTimeLimit(..)
  , WASMInstructionLimit(..)
    -- * Execution
  , executeWASM
  , executeWASMWithImports
    -- * Results
  , WASMResult(..)
  , WASMError(..)
    -- * Host Function Imports
  , HostFunction(..)
  , WASMImports(..)
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

{-| WASM sandbox configuration.

@
  record WASMConfig where
    constructor MkConfig
    wasmBytes      : ByteString      -- WASM module bytes
    memoryLimitMB  : WASMMemoryLimit -- Maximum linear memory
    timeLimitMs    : WASMTimeLimit   -- Maximum execution time
    instructionLimit : WASMInstructionLimit -- Max instructions
    imports        : WASMImports     -- Host function imports
    wasiEnabled    : Bool            -- Enable WASI (controlled)
@
-}
type WASMConfig =
  { wasmBytes :: String  -- Base64-encoded WASM bytes
  , memoryLimitMB :: Int  -- Maximum memory in MB (default: 128)
  , timeLimitMs :: Int    -- Maximum execution time in ms (default: 5000)
  , instructionLimit :: Maybe Int  -- Max instructions (None = unlimited)
  , imports :: WASMImports
  , wasiEnabled :: Boolean
  }

{-| Memory limit for WASM execution.
-}
type WASMMemoryLimit = Int

{-| Time limit for WASM execution.
-}
type WASMTimeLimit = Int

{-| Instruction limit for WASM execution.
-}
type WASMInstructionLimit = Maybe Int

-- ============================================================================
-- HOST FUNCTION IMPORTS
-- ============================================================================

{-| Host function that can be imported into WASM.

Only explicitly granted functions are available to WASM code.
-}
data HostFunction
  = ConsoleLog      -- console.log(string) -> void
  | ConsoleError    -- console.error(string) -> void
  | GetTimestamp    -- get_timestamp() -> i64
  | RandomBytes     -- random_bytes(count: i32) -> array<i8>
  | ReadFile        -- read_file(path: string) -> string | null
  | WriteFile       -- write_file(path: string, content: string) -> bool

derive instance eqHostFunction :: Eq HostFunction
derive instance ordHostFunction :: Ord HostFunction

{-| Set of host functions available to WASM.
-}
type WASMImports =
  { consoleLog :: Boolean
  , consoleError :: Boolean
  , getTimestamp :: Boolean
  , randomBytes :: Boolean
  , readFile :: Boolean
  , writeFile :: Boolean
  }

-- Default: no imports (maximum security)
defaultImports :: WASMImports
defaultImports =
  { consoleLog: false
  , consoleError: false
  , getTimestamp: false
  , randomBytes: false
  , readFile: false
  , writeFile: false
  }

-- ============================================================================
-- EXECUTION RESULTS
-- ============================================================================

{-| Result of WASM execution.
-}
data WASMResult
  = Success String  -- Output string
  | Error WASMError -- Error details

{-| WASM execution error.
-}
data WASMError
  = InvalidWASM String           -- WASM module invalid
  | MemoryLimitExceeded Int       -- Exceeded memory limit (MB)
  | TimeLimitExceeded Int         -- Exceeded time limit (ms)
  | InstructionLimitExceeded Int  -- Exceeded instruction limit
  | Trap String                   -- WASM trap (runtime error)
  | ImportNotFound String         -- Required import not found
  | HostFunctionError String      -- Host function error

derive instance eqWASMError :: Eq WASMError
derive instance eqWASMResult :: Eq WASMResult

-- ============================================================================
-- EXECUTION
-- ============================================================================

{-| Execute WASM module with default configuration.

Uses maximum security settings (no imports, strict limits).
-}
executeWASM :: WASMConfig -> Aff WASMResult
executeWASM config = executeWASMWithImports config defaultImports

{-| Execute WASM module with custom imports.

Validates WASM module, sets up sandbox, executes with resource limits,
and returns result.
-}
executeWASMWithImports :: WASMConfig -> WASMImports -> Aff WASMResult
executeWASMWithImports config imports = do
  result <- liftEffect $ executeWASMImpl config imports
  pure $ case result of
    Left err -> Error err
    Right output -> Success output

-- FFI implementation using wasmtime
foreign import executeWASMImpl :: WASMConfig -> WASMImports -> Effect (Either WASMError String)
