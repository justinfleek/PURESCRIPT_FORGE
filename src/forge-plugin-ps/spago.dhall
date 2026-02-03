{ name = "forge-sidepanel-plugin-ps"
, dependencies = 
  [ "prelude"
  , "effect"
  , "aff"
  , "either"
  , "maybe"
  , "argonaut"
  , "spec"
  , "quickcheck"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "MIT"
}
