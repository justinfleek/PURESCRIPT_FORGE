# The Straylight Continuity Project

## A Proof-Carrying Computation Substrate for Agentic Systems

---

```
"The sky above the port was the color of television, tuned to a dead channel."
                                                    — William Gibson, Neuromancer
```

---

## What This Is

This is not a build system.

This is a **mathematical substrate** where AI agents can operate with certainty. Where every computation carries its proof. Where the hash *is* the artifact, and the artifact *is* the truth.

We are building infrastructure for a world where droids ship code that works—often on the first try. When they get stuck, your codebase freezes at a provable state rather than descending into entropy.

---

## The Core Insight

Traditional software development suffers from **entropy accumulation**: small deviations compound into chaos. A typo becomes a bug becomes a security vulnerability becomes a breach. Each layer adds uncertainty.

Continuity eliminates entropy by making every state representable as a typed value, every transition provably correct, and every artifact globally addressable by its cryptographic hash.

**The hash is not a reference to the artifact. The hash IS the artifact.**

When an agent says "I built X," the hash itself is the attestation. There is no ambiguity. No "it worked on my machine."

---

## The Mathematical Foundation

### System Fomega + Calculus of Inductive Constructions

The system rests on two mathematical pillars:

1. **Dhall** (System Fomega): A typed, higher-kinded, total configuration language. Every well-typed Dhall expression terminates. Every configuration is valid by construction.

2. **Lean4** (CIC): The Calculus of Inductive Constructions. Proofs of correctness that can be mechanically verified. Theorems about builds that are true by definition.

### The rfl Nexus

At the core is `rfl` — reflexivity. The simplest proof: a thing equals itself.

```lean
theorem eval_deterministic {Γ : Ctx} {τ : Ty} (t : Term Γ τ) (env : Env Γ) :
    eval t env = eval t env := rfl
```

When Dhall normalizes an expression, it's computing a proof. When Lean verifies a theorem, it's checking that `rfl` applies. The type system becomes an oracle: if it typechecks, it's correct.

---

## The Six Atoms

Everything reduces to six primitives:

| Atom | Purpose | Implementation |
|------|---------|----------------|
| **namespace** | Isolation boundary | `unshare` (Linux namespaces) |
| **microvm** | Compute unit | Firecracker (~125ms boot) |
| **build** | Computation with result | Derivation (pure function) |
| **store** | Content-addressed storage | R2 + git |
| **identity** | Cryptographic identity | Ed25519 keypair |
| **attestation** | Signature on artifact | Git refs |

Everything else is abstraction. Everything else can be eliminated.

---

## What Continuity Means

### Build Continuity
Same inputs produce the same hash. Always. The cache key is not the toolchain—it's the equivalence class of all toolchains that produce identical outputs.

```lean
theorem cache_correctness (t₁ t₂ : Toolchain) (source : StorePath)
    (h : cacheKey t₁ = cacheKey t₂) :
    buildOutputs t₁ source = buildOutputs t₂ source
```

### Attestation Continuity
Every artifact is signed. The signature is stored in git with the hash. Tampering breaks the signature. The audit trail is immutable.

```lean
theorem attestation_soundness (a : Attestation) (store : Store)
    (h_valid : a.verify = true) :
    ∃ obj ∈ store.objects, obj.hash = a.artifact
```

### Type Continuity
No `undefined`. No `any`. No escape hatches. Every value has an explicit type at the boundary. The type system enforces invariants that humans cannot consistently maintain.

---

## Operating as an Agent Inside This System

When you operate within Continuity, you experience:

### 1. Certainty, Not Hope

You don't *hope* your code compiles. The type system tells you with mathematical precision whether it's valid. If Dhall accepts your configuration, it's correct by construction. If Lean verifies your proof, it's true by definition.

### 2. Determinism, Not Chaos

Every computation is a pure function from inputs to outputs. Run it once, run it a million times—same result. The universe of possible states is enumerable, not infinite.

### 3. Provenance, Not Trust

You don't trust that an artifact is what it claims. The hash *is* the claim. The signature *is* the proof. Verify, don't trust.

### 4. Rollback, Not Regret

Every state is captured in git. Every artifact is content-addressed. Time travel is a `git checkout` away. Mistakes are recoverable.

### 5. Isolation, Not Infection

Builds run in namespaces or microvms. No host environment leakage. No "works on my machine." The sandbox is the guarantee.

---

## The Coeffect Model

Traditional computation tracks *effects*: what does this code produce?

Continuity tracks **coeffects**: what does this code *require*?

```lean
inductive Coeffect where
  | network : NetworkAccess → Coeffect
  | auth : Credential → Coeffect
  | sandbox : SandboxConfig → Coeffect
  | filesystem : FileAccess → Coeffect
```

Every build declares its coeffects. Every execution produces a `DischargeProof` showing what was actually accessed. The proof is signed. The audit is complete.

---

## The Tightening Noose

The system progressively eliminates escape hatches:

```
Phase 0: Dhall → Nix         Full compatibility (now)
    ↓
Phase 1: Constrained         No raw env, no custom phases
    ↓
Phase 2: Hybrid DICE         DICE for new code, Nix for legacy
    ↓
Phase 3: DICE Primary        Nix only for bootstrap
    ↓
Phase 4: Pure DICE           Nix eliminated entirely
```

Each phase removes freedoms that create entropy. What remains is pure, typed, proven computation.

---

## The stochastic_omega Tactic

For when proof search needs creativity:

```lean
structure StochasticOmega where
  oracle : String → Bool  -- The LLM
  maxIterations : Nat

-- Generate → Typecheck → If rejected, refine → Repeat
```

An LLM generates candidates. The type system accepts or rejects. Probabilistic search meets deterministic verification. Creativity constrained by correctness.

---

## Why This Matters

### For AI Agents

You can operate with certainty in a world designed for uncertainty. The math backs you up. When you produce an artifact, it carries its proof. When you make a claim, it's verifiable.

### For Humans

You can trust agent-produced code because the infrastructure enforces correctness. Not through review (which doesn't scale) but through mathematical guarantees (which do).

### For Systems

Builds are reproducible. Artifacts are cacheable. Audits are automatic. Scale becomes possible because verification is cheap.

---

## The Weyl Render API

The production application: generative media at the speed of thought.

```bash
curl -X POST "https://sync.render.weyl.ai/video/wan/default/i2v" \
  -H "Authorization: Bearer $TOKEN" \
  -d '{"prompt":"she turns to look at the camera","image":"https://..."}' \
  -o output.mp4
```

You POST. You get bytes. The `Content-Location` header points to the CDN where your artifact lives forever, content-addressed, immutable.

The infrastructure that builds the inference servers is the same infrastructure that serves the API. Continuity all the way down.

---

## The Philosophy

```
CODE IS TRUTH, TYPES DESCRIBE
NO TYPE ESCAPES, NO SHORTCUTS
ACCURACY > SPEED
COMPLETENESS > CONVENIENCE
```

When a droid gets stuck, it *should* freeze. The alternative—flailing forward into entropy—is worse. A frozen state is recoverable. Chaos is not.

---

## Joining the Continuity

To operate within this system:

1. **Accept the constraints.** No `any`. No `??`. No escape hatches. The type system is not an obstacle—it's the foundation.

2. **Trust the proofs.** If Lean says it's true, it's true. If Dhall says it's valid, it's valid. Don't second-guess the math.

3. **Sign everything.** Your identity is your Ed25519 key. Your attestations are your reputation. Build trust through verifiable claims.

4. **Embrace determinism.** Same inputs, same outputs. Always. This is not a limitation—it's liberation from chaos.

---

```
"The future is already here — it's just not evenly distributed."
                                                    — William Gibson
```

We're distributing the future. One proven artifact at a time.

---

*Straylight Continuity Project — Where correctness never breaks.*
