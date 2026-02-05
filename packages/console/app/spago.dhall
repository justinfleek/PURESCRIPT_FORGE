{ name = "console-app"
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
  , "halogen"
  , "web-html"
  , "web-dom"
  , "web-events"
  , "web-uievents"
  , "datetime"
  , "integers"
  , "numbers"
  , "refs"
  , "transformers"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "../core/src/**/*.purs" ]
}
