{ name = "nexus-bridge-server"
, dependencies = 
  [ "prelude"
  , "effect"
  , "console"
  , "either"
  , "maybe"
  , "aff"
  , "argonaut"
  , "argonaut-codecs"
  , "arrays"
  , "strings"
  , "foreign"
  , "refs"
  ]
, packages = https://github.com/purescript/package-sets/releases/download/psc-0.15.11-20240214/packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "MIT"
}
