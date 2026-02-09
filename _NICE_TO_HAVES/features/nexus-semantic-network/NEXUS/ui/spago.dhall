{ name = "nexus-ui"
, dependencies = 
  [ "prelude"
  , "effect"
  , "aff"
  , "aff-class"
  , "halogen"
  , "halogen-hooks"
  , "either"
  , "maybe"
  , "arrays"
  , "strings"
  ]
, packages = https://github.com/purescript/package-sets/releases/download/psc-0.15.11-20240214/packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
}
