{ name = "nexus-database-layer-ps"
, dependencies = 
  [ "aff"
  , "argonaut"
  , "argonaut-codecs"
  , "effect"
  , "prelude"
  , "psci-support"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
