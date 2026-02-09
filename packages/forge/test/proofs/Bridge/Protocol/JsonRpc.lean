-- | JSON-RPC 2.0 Protocol Compliance Proofs
-- | Formal verification of protocol invariants
import Lean

namespace Bridge.Protocol.JsonRpc

-- | JSON-RPC version
def jsonrpcVersion : String := "2.0"

-- | JSON-RPC request structure
structure JsonRpcRequest where
  jsonrpc : String
  id : Option (Sum String ℕ)
  method : String
  params : Option String
  deriving Repr

-- | JSON-RPC response structure
structure JsonRpcResponse where
  jsonrpc : String
  id : Option (Sum String ℕ)
  result : Option String
  error : Option JsonRpcError
  deriving Repr

-- | JSON-RPC error structure
structure JsonRpcError where
  code : ℤ
  message : String
  data : Option String
  deriving Repr

-- | Request validity: version must be "2.0"
def JsonRpcRequest.valid (req : JsonRpcRequest) : Prop :=
  req.jsonrpc = jsonrpcVersion ∧ req.method.length > 0

-- | Response validity: version must be "2.0", result XOR error
def JsonRpcResponse.valid (res : JsonRpcResponse) : Prop :=
  res.jsonrpc = jsonrpcVersion ∧
  (res.result.isSome ∧ res.error.isNone) ∨
  (res.result.isNone ∧ res.error.isSome)

-- | Error code validity: standard JSON-RPC error codes
def JsonRpcError.validCode (code : ℤ) : Prop :=
  code = -32700 ∨  -- Parse error
  code = -32600 ∨  -- Invalid Request
  code = -32601 ∨  -- Method not found
  code = -32602 ∨  -- Invalid params
  code = -32603 ∨  -- Internal error
  (-32099 ≤ code ∧ code ≤ -32000)  -- Server error range

-- | Theorem: Valid request has correct version
theorem validRequestHasVersion (req : JsonRpcRequest) (hValid : JsonRpcRequest.valid req) :
  req.jsonrpc = jsonrpcVersion := by
  exact hValid.1

-- | Theorem: Valid request has non-empty method
theorem validRequestHasMethod (req : JsonRpcRequest) (hValid : JsonRpcRequest.valid req) :
  req.method.length > 0 := by
  exact hValid.2

-- | Theorem: Valid response has correct version
theorem validResponseHasVersion (res : JsonRpcResponse) (hValid : JsonRpcResponse.valid res) :
  res.jsonrpc = jsonrpcVersion := by
  exact hValid.1

-- | Theorem: Valid response has result XOR error
theorem validResponseResultXorError (res : JsonRpcResponse) (hValid : JsonRpcResponse.valid res) :
  (res.result.isSome ∧ res.error.isNone) ∨
  (res.result.isNone ∧ res.error.isSome) := by
  exact hValid.2

-- | Request-response matching: IDs must match
def requestResponseMatch (req : JsonRpcRequest) (res : JsonRpcResponse) : Prop :=
  req.id = res.id

-- | Theorem: Matching request-response have same ID
theorem matchingRequestResponseSameId
  (req : JsonRpcRequest)
  (res : JsonRpcResponse)
  (hMatch : requestResponseMatch req res) :
  req.id = res.id := by
  exact hMatch

-- | Error response validity
def JsonRpcError.valid (err : JsonRpcError) : Prop :=
  JsonRpcError.validCode err.code ∧ err.message.length > 0

-- | Theorem: Valid error has valid code
theorem validErrorHasValidCode (err : JsonRpcError) (hValid : JsonRpcError.valid err) :
  JsonRpcError.validCode err.code := by
  exact hValid.1

-- | Theorem: Valid error has non-empty message
theorem validErrorHasMessage (err : JsonRpcError) (hValid : JsonRpcError.valid err) :
  err.message.length > 0 := by
  exact hValid.2
