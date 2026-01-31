# System Architecture

## The Straylight Cube

```
                        PROVEN (rfl)
                            │
             Lean ─────────┼────────── Liquid Haskell
               │           │                 │
        TOTAL  ├───────────┼─────────────────┤  ESCAPE
               │           │                 │
           Dhall           │            PureScript
                           │              Haskell
                           │                 │
                           ├─────────────────┤─── Rust
                           │
                  stochastic_omega
                     (rfl oracle)
                          ↓
             WASM (portable)    C (native/kernel)
               ↓                       ↓
           builtins.wasm           isospin
            (sandbox)            (microvm + GPU)
```

Languages form a **coset**: same semantics, different tradeoffs. PureScript (fast iteration), Haskell (native performance), Rust (systems), Lean (proven correctness).

---

## Layer Model

### Layer 0: Mathematical Foundations

```
┌─────────────────────────────────────────────────────────────┐
│  CALCULUS OF INDUCTIVE CONSTRUCTIONS (Lean4)                │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  continuity_correctness theorem                         ││
│  │  ├── cache_correctness    (quotient types)              ││
│  │  ├── hermetic_build       (isolation_monotonic axiom)   ││
│  │  ├── offline_build        (store.contains predicate)    ││
│  │  └── attestation_soundness (ed25519_unforgeable axiom)  ││
│  └─────────────────────────────────────────────────────────┘│
│  SYSTEM FOMEGA (Dhall)                                      │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  Typed configuration: Target, Toolchain, Action, Rule   ││
│  │  Total evaluation: always terminates                    ││
│  │  Higher-kinded types: abstractions over type families   ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### Layer 1: Build Specification

```
┌─────────────────────────────────────────────────────────────┐
│  BUILD.dhall                                                │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  let straylight_core = Rust.library {                   ││
│  │      name = "straylight-core",                          ││
│  │      srcs = ["src/lib.rs", "src/store.rs"],            ││
│  │      deps = ["//vendor:tokio", "//vendor:serde"],       ││
│  │      edition = RustEdition.Edition2024,                 ││
│  │      crate_type = CrateType.RLib                        ││
│  │  }                                                      ││
│  └─────────────────────────────────────────────────────────┘│
│                            ↓                                │
│                    dhall --typecheck                        │
│                            ↓                                │
│                    dhall --normalize                        │
│                            ↓                                │
│                      JSON / Actions                         │
└─────────────────────────────────────────────────────────────┘
```

### Layer 2: Build Execution (DICE / Buck2)

```
┌─────────────────────────────────────────────────────────────┐
│  DISTRIBUTED INCREMENTAL COMPILATION ENVIRONMENT            │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  Action Graph                                           ││
│  │  ├── compile(src/lib.rs) → lib.rlib                     ││
│  │  ├── compile(src/store.rs) → store.rlib                 ││
│  │  └── link([lib.rlib, store.rlib]) → libstraylight.so   ││
│  └─────────────────────────────────────────────────────────┘│
│                            ↓                                │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  Execution Engine                                       ││
│  │  ├── Local (namespace isolation)                        ││
│  │  ├── Remote (NativeLink CAS + scheduler)                ││
│  │  └── MicroVM (Firecracker / Isospin)                    ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### Layer 3: Content-Addressed Storage

```
┌─────────────────────────────────────────────────────────────┐
│  STORE                                                      │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  R2 (Cloudflare)                                        ││
│  │  ca://sha256:3a7bd3e2...  →  [artifact bytes]          ││
│  │  ca://sha256:8f4c1b9a...  →  [artifact bytes]          ││
│  └─────────────────────────────────────────────────────────┘│
│  ┌─────────────────────────────────────────────────────────┐│
│  │  Git (Attestations)                                     ││
│  │  refs/attestations/sha256:3a7bd3e2  →  [signature]     ││
│  │  refs/attestations/sha256:8f4c1b9a  →  [signature]     ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### Layer 4: API Surface (Weyl Render)

```
┌─────────────────────────────────────────────────────────────┐
│  sync.render.weyl.ai                                        │
│  ├── POST /video/{family}/{model}/{task}                    │
│  ├── POST /image/{family}/{model}/{task}                    │
│  └── WebSocket /ws (streaming frames)                       │
│                                                             │
│  async.render.weyl.ai                                       │
│  ├── POST /queue (submit job)                               │
│  ├── GET /jobs/{id} (poll status)                           │
│  └── GET /jobs/{id}/events (SSE stream)                     │
│                                                             │
│  cdn.render.weyl.ai                                         │
│  └── GET /a/{asset_id} (immutable delivery)                 │
└─────────────────────────────────────────────────────────────┘
```

---

## Component Map

### Core Infrastructure (`aleph-b7r6-continuity-0x08/`)

```
aleph-b7r6-continuity-0x08/
├── nix/
│   ├── prelude/                    # Functional library (100+ functions)
│   │   ├── functions.nix           # map, filter, fold, maybe, either
│   │   ├── lib.nix                 # nixpkgs compatibility shim
│   │   ├── stdenv.nix              # Standard environment matrix
│   │   ├── toolchain.nix           # Language toolchain configs
│   │   ├── schemas.nix             # Type schemas
│   │   ├── gpu.nix                 # CUDA/GPU architecture metadata
│   │   └── wasm-plugin.nix         # WASM package compilation
│   │
│   ├── overlays/                   # Nixpkgs extensions
│   │   ├── nvidia-sdk/             # CUDA, cuDNN, TensorRT, NCCL
│   │   ├── libmodern/              # Modern C++ libraries (fmt, abseil)
│   │   ├── container/              # OCI, Firecracker, namespace tools
│   │   ├── haskell.nix             # GHC customizations
│   │   └── llvm-git.nix            # LLVM from source
│   │
│   ├── modules/flake/              # Flake-parts modules
│   │   ├── build/                  # Buck2 integration
│   │   ├── nv-sdk.nix              # NVIDIA SDK module
│   │   ├── lre.nix                 # Local Remote Execution
│   │   ├── container/              # Container builds
│   │   └── prelude.nix             # Prelude module
│   │
│   ├── packages/                   # Typed package definitions
│   │   ├── *.hs                    # Haskell DSL packages
│   │   └── *.wasm                  # Compiled WASM modules
│   │
│   └── checks/                     # Verification suite
│       ├── properties.nix          # Property tests
│       ├── toolchains.nix          # Toolchain tests
│       └── scripts/                # Test scripts
│
├── src/
│   ├── armitage/                   # Build orchestration tool
│   │   ├── Armitage/
│   │   │   ├── Builder.hs          # Build execution
│   │   │   ├── CAS.hs              # Content-addressable storage
│   │   │   ├── RE.hs               # Remote execution
│   │   │   ├── Store.hs            # Nix store interface
│   │   │   └── Trace.hs            # Execution tracing
│   │   ├── dhall/                  # Dhall schemas
│   │   └── proto/                  # Remote execution protos
│   │
│   └── examples/                   # Language examples
│       ├── lean-continuity/        # Lean4 proofs
│       ├── haskell/                # Haskell examples
│       ├── rust/                   # Rust examples
│       └── nv/                     # CUDA examples
│
├── docs/rfc/                       # Architecture decisions
│   ├── aleph-001-standard-nix.md   # Nix conventions
│   ├── aleph-002-lint.md           # Linting rules
│   ├── aleph-003-prelude.md        # Prelude design
│   ├── aleph-004-typed-unix.md     # Typed shell
│   ├── aleph-007-formalization.md  # CA derivations, typed DSL
│   └── aleph-008-continuity/       # Continuity project
│       ├── README.md               # Vision document
│       ├── ROADMAP.md              # Phase timeline
│       ├── continuity.lean         # Core proofs
│       └── dhall/                  # Type definitions
│
└── linter/                         # Static analysis
    └── rules/                      # 18 lint rules
```

### Service Layer (`src/`)

```
src/
├── rules-ps/                       # PureScript: Application logic
├── rules-hs/                       # Haskell: Performance-critical
├── rules-lean/                     # Lean4: Correctness proofs
│
├── render-api-ps/                  # API endpoint handler
├── render-billing-hs/              # Billing service
├── render-cas-hs/                  # Content-addressable storage
├── render-gateway-hs/              # API gateway
├── render-config-dhall/            # Configuration management
│
├── bridge-analytics-hs/            # Analytics pipeline
├── bridge-database-hs/             # Database abstraction
├── bridge-server-ps/               # Server framework
│
├── opencode-types-ps/              # Type definitions
├── opencode-plugin-ps/             # Plugin system
├── opencode-proofs-lean/           # Correctness proofs
├── opencode-validator-hs/          # Validation engine
│
├── sidepanel-ps/                   # UI (PureScript/Halogen)
├── spec-loader-hs/                 # Spec file loader
├── compiler-pipeline/              # Compilation infrastructure
└── voice-engine/                   # Voice processing
```

---

## Data Flow

### Build Flow

```
                    ┌─────────────┐
                    │ BUILD.dhall │
                    └──────┬──────┘
                           │ dhall typecheck
                           ▼
                    ┌─────────────┐
                    │   Actions   │
                    └──────┬──────┘
                           │ DICE scheduler
                           ▼
              ┌────────────┴────────────┐
              │                         │
              ▼                         ▼
       ┌────────────┐           ┌────────────┐
       │   Local    │           │   Remote   │
       │ (namespace)│           │(NativeLink)│
       └─────┬──────┘           └──────┬─────┘
              │                         │
              └────────────┬────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │  Artifacts  │
                    │  (hashed)   │
                    └──────┬──────┘
                           │ upload
                           ▼
              ┌────────────┴────────────┐
              │                         │
              ▼                         ▼
       ┌────────────┐           ┌────────────┐
       │     R2     │           │    Git     │
       │  (bytes)   │           │(attestation│
       └────────────┘           └────────────┘
```

### API Request Flow

```
        Client
           │
           │ POST /video/wan/default/i2v
           ▼
    ┌─────────────┐
    │   Gateway   │ (render-gateway-hs)
    └──────┬──────┘
           │ validate + route
           ▼
    ┌─────────────┐
    │   Worker    │ (inference server)
    │  (Blackwell)│
    └──────┬──────┘
           │ generate
           ▼
    ┌─────────────┐
    │  Artifact   │ (mp4 bytes)
    └──────┬──────┘
           │ hash + upload
           ▼
    ┌─────────────┐
    │    CDN      │ (cdn.render.weyl.ai)
    └──────┬──────┘
           │
           ▼
        Client
    (bytes + Content-Location)
```

---

## Security Model

### Trust Boundaries

```
┌─────────────────────────────────────────────────────────────┐
│  TRUSTED COMPUTING BASE                                     │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  Lean4 proof checker                                    ││
│  │  Dhall type checker                                     ││
│  │  Ed25519 implementation (libsodium)                     ││
│  │  SHA256 implementation (OpenSSL)                        ││
│  │  Linux kernel (namespace isolation)                     ││
│  │  Firecracker hypervisor                                 ││
│  └─────────────────────────────────────────────────────────┘│
│                                                             │
│  VERIFIED BY TCB                                            │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  Dhall configurations                                   ││
│  │  Lean proofs                                            ││
│  │  Content-addressed artifacts                            ││
│  │  Signed attestations                                    ││
│  └─────────────────────────────────────────────────────────┘│
│                                                             │
│  UNTRUSTED (verified at runtime)                            │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  User-provided source code                              ││
│  │  External dependencies (verified by hash)               ││
│  │  Network responses (verified by signature)              ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### Identity Chain

```
Developer Ed25519 Key
         │
         │ signs
         ▼
┌─────────────────┐
│   Attestation   │
│  ┌─────────────┐│
│  │ artifact:   ││
│  │ sha256:abc  ││
│  │ timestamp:  ││
│  │ 2026-01-31  ││
│  │ signature:  ││
│  │ [ed25519]   ││
│  └─────────────┘│
└────────┬────────┘
         │
         │ stored in
         ▼
┌─────────────────┐
│      Git        │
│ refs/attest/... │
└─────────────────┘
```

---

## Scaling Model

### Horizontal Scaling

```
                        ┌─────────────────┐
                        │   Load Balancer │
                        └────────┬────────┘
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
            ▼                    ▼                    ▼
     ┌────────────┐       ┌────────────┐       ┌────────────┐
     │  Worker 1  │       │  Worker 2  │       │  Worker N  │
     │ (Blackwell)│       │ (Blackwell)│       │ (Blackwell)│
     └─────┬──────┘       └──────┬─────┘       └──────┬─────┘
           │                     │                    │
           └─────────────────────┼────────────────────┘
                                 │
                                 ▼
                        ┌─────────────────┐
                        │       R2        │
                        │ (content store) │
                        └─────────────────┘
```

### Build Caching

```
┌─────────────────────────────────────────────────────────────┐
│  CACHE HIERARCHY                                            │
│                                                             │
│  L1: Process-local (in-memory)                              │
│      ├── eval cache (Nix expressions)                       │
│      └── build outputs (recent)                             │
│                                                             │
│  L2: Machine-local (disk)                                   │
│      ├── /nix/store                                         │
│      └── Buck2 output dir                                   │
│                                                             │
│  L3: Cluster (NativeLink)                                   │
│      ├── CAS (content-addressed)                            │
│      └── Action cache (input hash → output)                 │
│                                                             │
│  L4: Global (R2)                                            │
│      └── Immutable artifact storage                         │
└─────────────────────────────────────────────────────────────┘
```

---

## Deployment Topology

```
┌─────────────────────────────────────────────────────────────┐
│  CONTROL PLANE                                              │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  api.render.weyl.ai                                     ││
│  │  ├── Model discovery                                    ││
│  │  ├── Upload management                                  ││
│  │  └── User authentication                                ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│  SYNC TIER (SLA-backed)                                     │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  sync.render.weyl.ai                                    ││
│  │  ├── Dedicated Blackwell nodes                          ││
│  │  ├── No queue (direct execution)                        ││
│  │  └── 503 if capacity exhausted                          ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│  ASYNC TIER (queue-backed)                                  │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  async.render.weyl.ai                                   ││
│  │  ├── Job queue (Redis/NATS)                             ││
│  │  ├── Worker pool (elastic)                              ││
│  │  └── SSE/WebSocket for progress                         ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│  DATA PLANE                                                 │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  cdn.render.weyl.ai                                     ││
│  │  ├── Cloudflare R2 (storage)                            ││
│  │  ├── Cloudflare CDN (edge)                              ││
│  │  └── Cache-forever semantics                            ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```
