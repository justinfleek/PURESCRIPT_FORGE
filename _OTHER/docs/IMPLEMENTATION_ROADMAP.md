# Implementation Roadmap: From Scaffold to Production

**Created**: 2026-01-31
**Based on**: Deep code audit of entire codebase

---

## Phase 0: Critical Path (Serve One Request)

**Goal:** Make `/video/wan/default/t2v` return actual video bytes.

### 0.1 Fix Gateway Routes

**File:** `src/render-gateway-hs/src/Render/Gateway/Server.hs`

```haskell
-- CURRENT (wrong):
("/v1/generate/video")

-- REQUIRED (matches OpenAPI):
("/video", family, model, task)
```

Tasks:
- [ ] Update route matching to `/{modality}/{family}/{model}/{task}`
- [ ] Extract family, model, task from path segments
- [ ] Add format query parameter parsing
- [ ] Add backend query parameter parsing

### 0.2 Implement Request Parsing

**File:** `src/render-gateway-hs/src/Render/Gateway/Server.hs`

Replace hardcoded values in `createJobFromRequest`:
- [ ] Add UUID generation (use `uuid` package)
- [ ] Extract customer ID from JWT/Bearer token
- [ ] Parse model family from path
- [ ] Parse model name from path
- [ ] Parse task from path
- [ ] Parse all request body fields per OpenAPI spec

### 0.3 Implement Backend Forwarding

**File:** `src/render-gateway-hs/src/Render/Gateway/Server.hs`

```haskell
forwardToBackend :: Backend -> QueuedJob -> IO ByteString
forwardToBackend backend job = do
  -- Actual implementation needed:
  -- 1. Serialize request to gRPC protobuf
  -- 2. Open connection to backend.beEndpoint
  -- 3. Send request
  -- 4. Stream response back
  -- 5. Return video/image bytes
```

Tasks:
- [ ] Add gRPC client dependency (grpc-haskell or http2-grpc)
- [ ] Define Triton inference protocol messages
- [ ] Implement streaming response handling
- [ ] Add timeout handling
- [ ] Wire up circuit breaker on failure

### 0.4 Set Up Test Backend

Options:
1. **Mock backend** - Returns test video bytes
2. **Triton with real model** - Requires GPU server
3. **TensorRT-LLM** - Requires setup

Minimum for testing:
- [ ] Create mock gRPC server that returns static video
- [ ] Test end-to-end flow

---

## Phase 1: Cryptographic Foundation

**Goal:** Implement actual signing and verification.

### 1.1 Add Crypto Dependencies

**File:** `src/render-cas-hs/package.yaml` or `.cabal`

```yaml
dependencies:
  - blake3
  - ed25519
  - base64-bytestring
```

### 1.2 Implement BLAKE3 Hashing

**File:** `src/render-cas-hs/src/Render/CAS/Client.hs`

```haskell
import qualified Crypto.Hash.BLAKE3 as BLAKE3

computeBlake3Hash :: ByteString -> ByteString
computeBlake3Hash = BLAKE3.hash 32  -- 32-byte hash
```

### 1.3 Implement Ed25519 Signing

**File:** `src/render-cas-hs/src/Render/CAS/Client.hs`

```haskell
import qualified Crypto.Sign.Ed25519 as Ed25519

-- Need key management:
data SigningConfig = SigningConfig
  { scSecretKey :: Ed25519.SecretKey
  , scPublicKey :: Ed25519.PublicKey
  }

signBatch :: SigningConfig -> ByteString -> IO ByteString
signBatch config bs = pure $ Ed25519.sign (scSecretKey config) bs

verifySignature :: Ed25519.PublicKey -> ByteString -> ByteString -> Bool
verifySignature = Ed25519.verify
```

### 1.4 Key Management

- [ ] Decide where keys are stored (env var, vault, file)
- [ ] Implement key loading at startup
- [ ] Add key rotation strategy

---

## Phase 2: Storage Layer

**Goal:** Actually persist to CAS.

### 2.1 CAS Upload

**File:** `src/render-cas-hs/src/Render/CAS/Client.hs`

```haskell
import Network.HTTP.Client

uploadToCAS :: CASClient -> ByteString -> ByteString -> ByteString -> IO (Either String Text)
uploadToCAS client hash content signature = do
  manager <- newManager defaultManagerSettings
  let url = Text.unpack (casEndpoint client) <> "/v1/objects/" <> show hash
  request <- parseRequest url
  let request' = request
        { method = "PUT"
        , requestBody = RequestBodyBS content
        , requestHeaders =
            [ ("Content-Type", "application/octet-stream")
            , ("X-Signature", signature)
            ]
        }
  response <- httpLbs request' manager
  case statusCode (responseStatus response) of
    201 -> pure (Right (Text.decodeUtf8 hash))
    _ -> pure (Left "Upload failed")
```

### 2.2 CAS Fetch

Similar pattern for GET requests.

### 2.3 R2 Backend

- [ ] Set up Cloudflare R2 bucket
- [ ] Configure CAS endpoint URL
- [ ] Add R2 credentials to config

---

## Phase 3: Job Management

**Goal:** Track actual job state.

### 3.1 Choose Storage

Options:
- Redis (fast, ephemeral)
- PostgreSQL (durable)
- In-memory STM TVar (development only)

### 3.2 Implement Job Storage

```haskell
data JobStore = JobStore
  { jsJobs :: TVar (Map JobId Job)
  }

getJob :: JobStore -> JobId -> STM (Maybe Job)
updateJob :: JobStore -> JobId -> (Job -> Job) -> STM ()
```

### 3.3 Wire Up Status Updates

- [ ] Update job status when enqueued
- [ ] Update job status when backend starts processing
- [ ] Update job status on completion/error
- [ ] Store output URL on completion

---

## Phase 4: Proofs (Honest Approach)

**Goal:** Either prove theorems or rename to invariants.

### Option A: Complete the Proofs

Each `admit`/`sorry` needs actual proof. This requires:
- Formalizing bubblewrap semantics
- Formalizing network namespace isolation
- Proving properties about our specific implementation

**Effort:** High (weeks to months)

### Option B: Rename to Runtime Invariants

More honest approach:

```lean
-- Before:
theorem sandbox_isolation : ... := by
  admit  -- Runtime invariant

-- After:
/-- Runtime invariant: sandbox creation ensures unique directories per agent.
    This is enforced by bubblewrap --bind mount configuration.
    Not proven in Lean; verified by integration tests. -/
axiom sandbox_isolation_invariant : ...
```

**Effort:** Low (documentation change)

---

## Phase 5: Analytics

### 5.1 ClickHouse Integration

- [ ] Set up ClickHouse instance
- [ ] Implement query functions
- [ ] Wire up metrics collection on request completion

### 5.2 Reconciliation

- [ ] Implement CAS query via DuckDB
- [ ] Implement delta comparison
- [ ] Add alerting on discrepancy

---

## Priority Order

1. **Phase 0** - Required to serve any request
2. **Phase 3** - Required for async API (`/queue`)
3. **Phase 1** - Required for audit compliance
4. **Phase 2** - Required for artifact persistence
5. **Phase 4** - Required for integrity claims
6. **Phase 5** - Required for billing

---

## Dependencies

```
Phase 0 (Gateway)
    │
    ├─► Phase 3 (Jobs) ─► Async API works
    │
    └─► Phase 1 (Crypto) ─► Phase 2 (CAS) ─► Phase 4 (Proofs)
                                              │
                                              └─► Phase 5 (Analytics)
```

---

## Minimum Viable Product

To have a **working demo**:

1. Phase 0.1-0.3 (gateway routes + forwarding)
2. Mock backend returning test video
3. Basic job tracking (in-memory)

This would allow:
```bash
curl -X POST "http://localhost:8080/video/wan/default/t2v" \
  -H "Content-Type: application/json" \
  -d '{"prompt": "test"}' \
  -o output.mp4
```

And receive actual bytes.

---

*This roadmap prioritizes working software over aspirational documentation.*
