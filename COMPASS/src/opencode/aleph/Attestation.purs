-- | Aleph Attestation System
-- |
-- | Attestations are cryptographically signed records that prove:
-- | - What was produced (content hash)
-- | - What was required (coeffects)
-- | - How requirements were satisfied (discharge proof)
-- | - Who ran it (ed25519 identity)
-- |
-- | This implements the attestation model from aleph-008:
-- | - Content-addressed storage in R2
-- | - Git for attestation records
-- | - ed25519 for identity and signing
module Aleph.Attestation
  ( -- Content addressing
    Hash(..)
  , mkHash
  , hashBytes
  , hashString
  , verifyHash
    -- Identity
  , Ed25519PublicKey(..)
  , Ed25519Signature(..)
  , Identity(..)
  , mkIdentity
    -- Attestation
  , Attestation(..)
  , mkAttestation
  , verifyAttestation
    -- Trust
  , TrustPolicy(..)
  , satisfies
  , lookup
    -- Artifact
  , Artifact(..)
  , ArtifactRef(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.String as String
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json)

import Aleph.Coeffect (Resource, DischargeProof)

-- ════════════════════════════════════════════════════════════════════════════
-- CONTENT ADDRESSING
-- ════════════════════════════════════════════════════════════════════════════

-- | SHA256 hash - the universal content address
-- |
-- | "The hash IS the artifact" - aleph-008
newtype Hash = Hash String

derive instance eqHash :: Eq Hash
derive instance ordHash :: Ord Hash
derive instance genericHash :: Generic Hash _
derive newtype instance showHash :: Show Hash
derive newtype instance encodeJsonHash :: EncodeJson Hash
derive newtype instance decodeJsonHash :: DecodeJson Hash

-- | Create a hash from a hex string (validates format)
mkHash :: String -> Either String Hash
mkHash s
  | String.length s /= 64 = Left "Hash must be 64 hex characters"
  | not (isHex s) = Left "Hash must be hexadecimal"
  | otherwise = Right (Hash s)
  where
    isHex str = String.null (String.dropWhile isHexChar str)
    isHexChar c = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

-- | Hash bytes (placeholder - would use crypto FFI)
hashBytes :: String -> Hash
hashBytes _ = Hash "0000000000000000000000000000000000000000000000000000000000000000"

-- | Hash a string (placeholder - would use crypto FFI)
hashString :: String -> Hash
hashString = hashBytes

-- | Verify content against hash
verifyHash :: Hash -> String -> Boolean
verifyHash expected content = hashString content == expected

-- ════════════════════════════════════════════════════════════════════════════
-- IDENTITY
-- ════════════════════════════════════════════════════════════════════════════

-- | Ed25519 public key (32 bytes, hex encoded)
newtype Ed25519PublicKey = Ed25519PublicKey String

derive instance eqEd25519PublicKey :: Eq Ed25519PublicKey
derive instance ordEd25519PublicKey :: Ord Ed25519PublicKey
derive instance genericEd25519PublicKey :: Generic Ed25519PublicKey _
derive newtype instance showEd25519PublicKey :: Show Ed25519PublicKey
derive newtype instance encodeJsonEd25519PublicKey :: EncodeJson Ed25519PublicKey

-- | Ed25519 signature (64 bytes, hex encoded)
newtype Ed25519Signature = Ed25519Signature String

derive instance eqEd25519Signature :: Eq Ed25519Signature
derive instance genericEd25519Signature :: Generic Ed25519Signature _
derive newtype instance showEd25519Signature :: Show Ed25519Signature
derive newtype instance encodeJsonEd25519Signature :: EncodeJson Ed25519Signature

-- | Identity with metadata
type Identity =
  { publicKey :: Ed25519PublicKey
  , name :: Maybe String        -- Human-readable name
  , org :: Maybe String         -- Organization
  , created :: Number           -- Unix timestamp
  }

-- | Create an identity
mkIdentity :: Ed25519PublicKey -> Identity
mkIdentity pk =
  { publicKey: pk
  , name: Nothing
  , org: Nothing
  , created: 0.0
  }

-- ════════════════════════════════════════════════════════════════════════════
-- ATTESTATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Cryptographically signed attestation
-- |
-- | This is the core record that proves a computation was run correctly.
-- | It binds together:
-- | - The output (content hash)
-- | - The requirements (coeffects)
-- | - The evidence (discharge proof)
-- | - The identity (who ran it)
-- | - The signature (proof of attestation)
type Attestation =
  { content :: Hash              -- What was produced
  , coeffects :: Resource        -- What was required
  , discharged :: DischargeProof -- How it was satisfied
  , identity :: Ed25519PublicKey -- Who ran it
  , timestamp :: Number          -- When
  , signature :: Ed25519Signature -- Cryptographic proof
  }

-- | Create an attestation (would sign with private key)
mkAttestation 
  :: Hash 
  -> Resource 
  -> DischargeProof 
  -> Ed25519PublicKey 
  -> Number 
  -> Attestation
mkAttestation content coeffects discharged identity timestamp =
  { content
  , coeffects
  , discharged
  , identity
  , timestamp
  , signature: Ed25519Signature "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
  }

-- | Verify an attestation's signature
verifyAttestation :: Attestation -> Boolean
verifyAttestation _ = true -- Placeholder - would verify ed25519 signature

-- ════════════════════════════════════════════════════════════════════════════
-- TRUST POLICY
-- ════════════════════════════════════════════════════════════════════════════

-- | Trust policy - who do we trust for attestations?
-- |
-- | This is explicit, not hidden in sandbox flags.
data TrustPolicy
  = TrustSelf                    -- I built it
  | TrustIdentity Ed25519PublicKey -- Trust this specific key
  | TrustOrg String              -- Trust all keys from this org
  | TrustMultiple Int            -- Require N independent attestations
  | TrustReproducible            -- Multiple attestations must have same hash

derive instance eqTrustPolicy :: Eq TrustPolicy
derive instance genericTrustPolicy :: Generic TrustPolicy _

instance showTrustPolicy :: Show TrustPolicy where
  show = genericShow

-- | Check if an attestation satisfies a trust policy
satisfies :: TrustPolicy -> Ed25519PublicKey -> Attestation -> Boolean
satisfies policy myKey att = case policy of
  TrustSelf -> att.identity == myKey
  TrustIdentity key -> att.identity == key
  TrustOrg _ -> true -- Would check org membership
  TrustMultiple _ -> true -- Would check attestation count
  TrustReproducible -> true -- Would check hash consistency

-- | Lookup artifact by hash with trust policy
lookup 
  :: Hash 
  -> TrustPolicy 
  -> Ed25519PublicKey 
  -> Array Attestation 
  -> Maybe Artifact
lookup hash policy myKey attestations =
  let matching = Array.filter (\a -> a.content == hash) attestations
      trusted = Array.filter (satisfies policy myKey) matching
  in case Array.head trusted of
    Nothing -> Nothing
    Just att -> Just (mkArtifact hash att)

-- ════════════════════════════════════════════════════════════════════════════
-- ARTIFACT
-- ════════════════════════════════════════════════════════════════════════════

-- | Content-addressed artifact reference
-- |
-- | Points to R2 storage: r2.straylight.cx/cas/{hash}
type ArtifactRef =
  { hash :: Hash
  , size :: Int           -- Size in bytes
  , mediaType :: String   -- MIME type
  }

-- | Artifact with attestation
type Artifact =
  { ref :: ArtifactRef
  , attestation :: Attestation
  }

-- | Create artifact from hash and attestation
mkArtifact :: Hash -> Attestation -> Artifact
mkArtifact hash att =
  { ref: { hash, size: 0, mediaType: "application/octet-stream" }
  , attestation: att
  }
