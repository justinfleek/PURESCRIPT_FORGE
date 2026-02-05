{ name = "console-core"
, dependencies =
  [ "prelude"
  , "effect"
  , "aff"
  , "maybe"
  , "either"
  , "arrays"
  , "strings"
  , "tuples"
  , "ordered-collections"
  , "foldable-traversable"
  , "foreign"
  , "foreign-object"
  , "datetime"
  , "integers"
  , "numbers"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
