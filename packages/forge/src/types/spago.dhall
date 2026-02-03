{ name = "forge-types-ps"
, dependencies = 
  [ "prelude"
  , "effect"
  , "aff"
  , "argonaut"
  , "argonaut-codecs"
  , "generics-rep"
  , "maybe"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
}
