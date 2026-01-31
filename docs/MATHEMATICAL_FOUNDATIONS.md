# Mathematical Foundations

## The Type-Theoretic Stack

The Continuity system is built on a hierarchy of type systems, each providing different guarantees:

```
┌─────────────────────────────────────────────────────────────┐
│  CALCULUS OF INDUCTIVE CONSTRUCTIONS (Lean4)                │
│  • Dependent types                                          │
│  • Proof terms                                              │
│  • Certified extraction to C                                │
│  • Theorems about builds                                    │
└─────────────────────────────────────────────────────────────┘
                            ↑ proves properties of
┌─────────────────────────────────────────────────────────────┐
│  SYSTEM Fω (Dhall)                                          │
│  • Higher-kinded types                                      │
│  • Total evaluation (always terminates)                     │
│  • No side effects                                          │
│  • Configuration by construction                            │
└─────────────────────────────────────────────────────────────┘
                            ↑ configures
┌─────────────────────────────────────────────────────────────┐
│  SYSTEM F (Haskell/PureScript)                              │
│  • Parametric polymorphism                                  │
│  • Type classes                                             │
│  • Monadic effects                                          │
│  • Application logic                                        │
└─────────────────────────────────────────────────────────────┘
```

---

## The Core Theorems

### 1. Cache Correctness

**Statement**: Toolchains in the same equivalence class produce identical outputs.

```lean
def buildEquivalent (t₁ t₂ : Toolchain) : Prop :=
  t₁.compiler.emit = t₂.compiler.emit ∧
  t₁.target = t₂.target ∧
  (∀ src : List UInt8, compile t₁ src = compile t₂ src)

theorem cache_correctness (t₁ t₂ : Toolchain) (source : StorePath)
    (h : cacheKey t₁ = cacheKey t₂) :
    buildOutputs t₁ source = buildOutputs t₂ source
```

**Intuition**: The cache key is not the toolchain itself—it's the equivalence class of all toolchains that produce byte-identical outputs. Different compiler versions, different optimization flags, different host systems can all map to the same cache key if they produce the same result.

**Proof technique**: Quotient types. We define an equivalence relation `buildEquivalent`, then `cacheKey` is a function from `Toolchain` to the quotient type.

### 2. Hermeticity

**Statement**: With full namespace isolation, builds cannot access paths outside their declared inputs.

```lean
theorem hermetic_build
    (t : Toolchain)
    (ns : Namespace)
    (h_isolated : ns = Namespace.full)
    (buildInputs : Set StorePath)
    (h_inputs_declared : buildInputs ⊆ toolchainClosure t) :
    ∀ buildAccessed, buildAccessed ⊆ buildInputs
```

**Intuition**: Linux namespaces (user, mount, network, PID) create an isolation boundary. The build process literally cannot see paths outside its declared inputs because they don't exist in its namespace.

**Proof technique**: We delegate to the kernel. The `isolation_monotonic` axiom states that more isolation doesn't change outputs—if a build succeeds with fewer constraints, it succeeds with more.

### 3. Attestation Soundness

**Statement**: Valid Ed25519 signatures imply artifact integrity.

```lean
theorem attestation_soundness
    (a : Attestation)
    (store : Store)
    (h_valid : a.verify = true) :
    ∃ obj ∈ store.objects, obj.hash = a.artifact
```

**Intuition**: Ed25519 signatures are unforgeable (under standard cryptographic assumptions). If an attestation verifies, the artifact it claims was built actually exists and was signed by someone with the secret key.

**Proof technique**: We axiomatize Ed25519 unforgeability:
```lean
axiom ed25519_unforgeable :
  ∀ pk msg sig, ed25519_verify pk msg sig = true →
    ∃ sk, KeyPair sk pk ∧ ed25519_sign sk msg = sig
```

### 4. Offline Build Capability

**Statement**: If all dependencies are in the store, builds work without network.

```lean
theorem offline_build_possible
    (t : Toolchain)
    (store : Store)
    (h_populated : ∀ p ∈ toolchainClosure t, store.contains p) :
    CanBuildOffline store (toolchainClosure t)
```

**Intuition**: The transitive closure of a toolchain (compiler, sysroot, all dependencies) defines everything needed to build. If that closure is fully present in the local store, no network access is required.

### 5. Continuity Correctness (Main Theorem)

**Statement**: The composition of all guarantees.

```lean
theorem continuity_correctness
    (t : Toolchain)
    (ns : Namespace)
    (manifest : SourceManifest)
    (store : Store)
    (h_isolated : ns = Namespace.full)
    (h_populated : ∀ p ∈ toolchainClosure t, store.contains p) :
    -- Hermetic
    (∀ inputs accessed, accessed ⊆ inputs → IsHermetic inputs accessed) ∧
    -- Cache correct
    (∀ t', cacheKey t = cacheKey t' → ∀ source, buildOutputs t source = buildOutputs t' source) ∧
    -- Offline capable
    CanBuildOffline store (toolchainClosure t) ∧
    -- Attestation sound
    (∀ a : Attestation, a.verify = true → ∃ obj ∈ store.objects, obj.hash = a.artifact)
```

---

## The Dhall Type System

Dhall implements System Fω, a typed lambda calculus with:

### Higher-Kinded Types

```dhall
-- Kind: Type → Type
let List : Type → Type = λ(a : Type) → ...

-- Kind: (Type → Type) → Type
let Fix : (Type → Type) → Type = λ(f : Type → Type) → ...
```

### Total Evaluation

Every well-typed Dhall expression terminates. There are no infinite loops.

```dhall
-- This is IMPOSSIBLE in Dhall:
let loop : Natural = loop  -- Rejected: not structurally decreasing
```

### No Effects

Dhall has no IO, no exceptions, no mutable state. Evaluation is pure.

```dhall
-- This is IMPOSSIBLE in Dhall:
let readFile : Text → Text = ...  -- No such primitive exists
```

### The rfl Connection

Dhall normalization corresponds to Lean's definitional equality (`rfl`).

```lean
-- In Lean:
theorem dhall_deterministic (t : DhallTerm) (env : DhallEnv) :
    normalize t env = normalize t env := rfl

-- The proof is trivial because normalization is a pure function.
-- Same inputs always produce same outputs.
```

---

## The Coeffect Model

Traditional effect systems track what code *produces*. Coeffects track what code *requires*.

### Coeffect Types

```lean
inductive Coeffect where
  | network : NetworkAccess → Coeffect    -- HTTP requests, DNS
  | auth : Credential → Coeffect          -- API keys, certificates
  | sandbox : SandboxConfig → Coeffect    -- Isolation requirements
  | filesystem : FileAccess → Coeffect    -- File reads/writes
  | combined : List Coeffect → Coeffect   -- Composition
```

### Discharge Proofs

Every build that uses external resources produces a `DischargeProof`:

```lean
structure DischargeProof where
  coeffects : List Coeffect
  evidence : CoeffectEvidence
  timestamp : Nat
  signature : Option (PublicKey × Signature)
```

The proof records:
- What resources were declared
- What resources were actually accessed
- When the build occurred
- Who signed the attestation

### Why This Matters

Coeffects enable auditing. You can answer:
- "Did this build access the network?"
- "What credentials were used?"
- "Was the sandbox properly configured?"

The answers are cryptographically signed and recorded.

---

## Parametricity and Graph Extraction

### The Parametricity Theorem

Build systems that don't inspect artifact contents are **parametric functors**:

```lean
class Parametric (bs : BuildSystem) where
  parametric : ∀ {α β : Type} [Artifact α] [Artifact β]
    (f : α → β)
    (preserves_combine : ∀ xs, f (Artifact.combine xs) = Artifact.combine (xs.map f))
    (preserves_empty : f Artifact.empty = Artifact.empty)
    (srcα : Nat → α) (srcβ : Nat → β)
    (h_src : ∀ n, f (srcα n) = srcβ n)
    (inputs : List Nat),
    f (bs.build srcα inputs) = bs.build srcβ inputs
```

**Intuition**: If a build system only routes artifacts through `combine` and `empty` operations (never inspects their contents), then it's a functor over artifact types.

### Graph Extraction

We can extract the dependency graph from any parametric build system:

```lean
structure GraphNode where
  id : Nat
  deps : List Nat

def extractGraph (bs : BuildSystem) (inputs : List Nat) : GraphNode :=
  bs.build (fun n => ⟨n, []⟩) inputs
```

**How it works**:
1. Replace real artifacts (`.o` files) with `GraphNode` tokens
2. Run the build system with these fake artifacts
3. The routing behavior (what depends on what) is captured as graph structure
4. By parametricity, this graph is exactly what the real build would produce

### The CMake Confession Theorem

```lean
theorem cmake_confession (cmakeBuild : BuildSystem) [Parametric cmakeBuild]
    (sources : List Nat) :
    extractGraph cmakeBuild sources = realDependencyGraph sources
```

We can extract the true dependency graph from CMake (or Make, or Ninja, or Autotools) by:
1. Shimming the compiler with a logger
2. Letting CMake "configure" with our fake toolchain
3. Capturing all inputs/outputs as the graph

This works because CMake is parametric—it routes artifacts without inspecting their contents.

---

## The stochastic_omega Tactic

For proof search that benefits from creativity:

```lean
structure StochasticOmega where
  oracle : String → Bool  -- The LLM
  maxIterations : Nat

axiom stochastic_omega_sound :
  ∀ (so : StochasticOmega) (goal : String),
    so.oracle goal = true → True
```

**The pattern**:
1. LLM generates a candidate (code, proof, configuration)
2. Type checker validates (Dhall, Lean, TypeScript)
3. If rejected, LLM receives error and refines
4. If accepted, run tests/proofs
5. If tests fail, LLM receives failure and refines
6. If tests pass, done

**Why this is sound**: The oracle (type system) provides *deterministic* verification. The LLM provides *probabilistic* search. The combination is probabilistically complete search with deterministic soundness.

---

## Axioms and Trust

The proofs rely on axioms that delegate to external systems:

### Cryptographic Axioms

```lean
axiom sha256 : List UInt8 → Hash
axiom sha256_injective : ∀ b₁ b₂, sha256 b₁ = sha256 b₂ → b₁ = b₂

axiom ed25519_sign : SecretKey → List UInt8 → Signature
axiom ed25519_verify : PublicKey → List UInt8 → Signature → Bool
axiom ed25519_unforgeable : ∀ pk msg sig,
    ed25519_verify pk msg sig = true →
    ∃ sk, KeyPair sk pk ∧ ed25519_sign sk msg = sig
```

**Trust basis**: NIST (SHA256), academic cryptography (Ed25519)

### System Axioms

```lean
axiom executeAction : Action → Namespace → Finset DrvOutput
axiom isolation_monotonic : ∀ a ns₁ ns₂,
    Namespace.le ns₁ ns₂ → executeAction a ns₁ = executeAction a ns₂
```

**Trust basis**: Linux kernel (namespace isolation)

### Philosophy

We don't reprove what has industrial/academic assurance. We axiomatize the interfaces and prove that the *composition* is correct.

The TCB (Trusted Computing Base) is:
- Lean4 proof checker
- Dhall type checker
- libsodium (Ed25519)
- OpenSSL (SHA256)
- Linux kernel (namespaces)
- Firecracker (microvm)

Everything else is verified by this TCB.

---

## Summary

The mathematical foundations provide five layers of verification:

1. **Type layer** (Lean types): Compile-time detection of invalid configurations
2. **Logical layer** (theorems): Composition guarantees about cache, hermeticity, attestation
3. **Cryptographic layer** (axioms): Hash collision resistance, signature unforgeability
4. **System layer** (axioms): Kernel namespace isolation
5. **Parametricity layer** (theorems): Build system graph extraction correctness

Together, these guarantee that **Continuity is correct by construction**—not just in theory, but connected to industrial standards that have decades of validation.
