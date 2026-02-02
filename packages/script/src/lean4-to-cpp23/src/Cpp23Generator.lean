-- Lean4 → C++23 Generator: Complete Implementation
import LeanIRParser
import ProofPreservation

-- | Generate C++23 from Lean IR with full support
def generateCpp23FromIR (irs : List LeanIR) : String :=
  let proofs = extractProofs irs
  let nonProofs = irs.filter fun ir => 
    match ir.type with
    | LeanType.proof _ => false
    | _ => true
  in
  "#include <string>\n" ++
  "#include <vector>\n" ++
  "#include <optional>\n" ++
  "#include <variant>\n" ++
  "#include <functional>\n" ++
  "#include <future>\n" ++
  "#include <concepts>\n" ++
  "#include <cstdint>\n" ++
  "#include <type_traits>\n" ++
  "\n" ++
  "namespace generated {\n" ++
  "\n" ++
  "// Regular functions\n" ++
  String.join (nonProofs.map generateCpp23) ++
  "\n" ++
  "} // namespace generated\n" ++
  "\n" ++
  "// Proof verification\n" ++
  generateProofVerificationHeader proofs

-- | Generate C++23 function with proof preservation (wrapper)
def generateCpp23WithProofWrapper (ir : LeanIR) : String :=
  ProofPreservation.generateCpp23WithProof ir
