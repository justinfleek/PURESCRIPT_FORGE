{ name = "console-core"
, dependencies =
  [ "prelude"
  , "effect"
  , "aff"
  , "maybe"
  , "either"
  , "arrays"
  , "strings"
  , "ordered-collections"
  , "foreign"
  , "datetime"
  , "integers"
  , "free"
  , "transformers"
  , "refs"
  , "enums"
  , "exceptions"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
