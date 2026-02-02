{ name = "nexus-agent-orchestrator"
, dependencies = 
  [ "prelude"
  , "effect"
  , "aff"
  , "either"
  , "maybe"
  , "argonaut"
  , "argonaut-codecs"
  , "arrays"
  , "strings"
  , "ordered-collections"
  ]
, packages = https://github.com/purescript/package-sets/releases/download/psc-0.15.11-20240214/packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
}
