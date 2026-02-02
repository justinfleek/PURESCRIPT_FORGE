{ name = "opencode-sidepanel"
, dependencies = 
  [ "prelude"
  , "effect"
  , "console"
  , "either"
  , "maybe"
  , "halogen"
  , "halogen-hooks"
  , "routing-duplex"
  , "routing-duplex-generic"
  , "datetime"
  , "aff"
  , "affjax"
  , "argonaut"
  , "argonaut-codecs"
  , "web-html"
  , "web-socket"
  , "arrays"
  , "generics-rep"
  , "unsafe-coerce"
  , "ordered-collections"
  , "spec"
  , "quickcheck"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "MIT"
}
