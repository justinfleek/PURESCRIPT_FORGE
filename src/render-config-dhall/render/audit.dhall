-- | Render Audit Configuration (Dhall)
-- | System Fω typing guarantees per render_specs.pdf §3.1

let StorageBackend = < R2 : { endpoint : Text, bucket : Text }
                     | S3Compatible : { endpoint : Text, bucket : Text }
                     | Nexus : { endpoint : Text, bucket : Text }
                     >

let RetentionPolicy = { days : Natural, legalHold : Bool }

let BillingConfig = { enabled : Bool, granularity : Text }

let ComplianceLevel = < Prudent | Auditable >

let AuditConfig = { storage : StorageBackend
                  , retention : RetentionPolicy
                  , billing : BillingConfig
                  , compliance : ComplianceLevel
                  }

in  AuditConfig
