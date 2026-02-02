{ name = "forge-rules-ps"
, dependencies = 
  [ "prelude"
  , "effect"
  , "console"
  , "either"
  , "maybe"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
}
