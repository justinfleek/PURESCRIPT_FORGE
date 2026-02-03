{ name = "forge-types-ps"
, dependencies = 
  [ "prelude"
  , "effect"
  , "aff"
  , "argonaut"
  , "argonaut-codecs"
  , "maybe"
  , "either"
  , "foreign-object"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
}
