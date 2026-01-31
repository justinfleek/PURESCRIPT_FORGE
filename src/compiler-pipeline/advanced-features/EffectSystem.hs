{-# LANGUAGE OverloadedStrings #-}
module EffectSystem where

import qualified Data.Text as T
import GHC.Core
import GHC.Core.Type

-- | Effect type representation
data EffectType
  = EffectPure  -- Pure computation
  | EffectIO  -- IO effect
  | EffectExcept String  -- Exception effect
  | EffectState String  -- State effect
  | EffectReader String  -- Reader effect
  | EffectWriter String  -- Writer effect
  | EffectAsync  -- Async effect
  | EffectRow [EffectType]  -- Row of effects (PureScript style)

-- | Extract effect from type
extractEffect :: Type -> EffectType
extractEffect ty = case splitTyConApp_maybe ty of
  Just (tycon, _) -> 
    let name = show $ tyConName tycon
    in case name of
      "IO" -> EffectIO
      "Effect" -> EffectIO
      "ExceptT" -> EffectExcept "error"
      "StateT" -> EffectState "state"
      "ReaderT" -> EffectReader "env"
      "WriterT" -> EffectWriter "log"
      _ -> EffectPure
  Nothing -> EffectPure

-- | Generate C++23 for effect type
effectToCpp23 :: EffectType -> T.Text
effectToCpp23 EffectPure = "template<typename T> using Pure = T;"
effectToCpp23 EffectIO = T.unlines
  [ "template<typename T>"
  , "class IO {"
  , "private:"
  , "  std::function<T()> action_;"
  , "public:"
  , "  explicit IO(std::function<T()> action) : action_(std::move(action)) {}"
  , "  T runIO() const { return action_(); }"
  , "};"
  ]
effectToCpp23 (EffectExcept errType) = T.unlines
  [ "template<typename T>"
  , "class Except {"
  , "private:"
  , "  std::variant<T, std::string> value_;"
  , "public:"
  , "  static Except<T> success(T value) {"
  , "    return Except<T>(std::variant<T, std::string>(std::in_place_index<0>, std::move(value)));"
  , "  }"
  , "  static Except<T> failure(std::string error) {"
  , "    return Except<T>(std::variant<T, std::string>(std::in_place_index<1>, std::move(error)));"
  , "  }"
  , "  bool isSuccess() const { return value_.index() == 0; }"
  , "  T getValue() const { return std::get<0>(value_); }"
  , "  std::string getError() const { return std::get<1>(value_); }"
  , "};"
  ]
effectToCpp23 (EffectState stateType) = T.unlines
  [ "template<typename T, typename S>"
  , "class State {"
  , "private:"
  , "  std::function<std::pair<T, S>(S)> action_;"
  , "public:"
  , "  explicit State(std::function<std::pair<T, S>(S)> action) : action_(std::move(action)) {}"
  , "  std::pair<T, S> runState(S state) const { return action_(state); }"
  , "};"
  ]
effectToCpp23 (EffectReader envType) = T.unlines
  [ "template<typename T, typename E>"
  , "class Reader {"
  , "private:"
  , "  std::function<T(E)> action_;"
  , "public:"
  , "  explicit Reader(std::function<T(E)> action) : action_(std::move(action)) {}"
  , "  T runReader(E env) const { return action_(env); }"
  , "};"
  ]
effectToCpp23 (EffectWriter logType) = T.unlines
  [ "template<typename T, typename L>"
  , "class Writer {"
  , "private:"
  , "  std::pair<T, L> value_;"
  , "public:"
  , "  Writer(T value, L log) : value_(std::move(value), std::move(log)) {}"
  , "  T getValue() const { return value_.first; }"
  , "  L getLog() const { return value_.second; }"
  , "};"
  ]
effectToCpp23 EffectAsync = T.unlines
  [ "template<typename T>"
  , "using Async = std::future<T>;"
  , ""
  , "template<typename T>"
  , "auto async(std::function<T()> computation) -> Async<T> {"
  , "  return std::async(std::launch::async, computation);"
  , "}"
  ]
effectToCpp23 (EffectRow effects) = T.unlines
  [ "// Effect row: " <> T.intercalate ", " (map showEffect effects)
  , "template<typename T>"
  , "class EffectRow {"
  , "  // Combined effect handling"
  , "};"
  ]

showEffect :: EffectType -> T.Text
showEffect EffectPure = "Pure"
showEffect EffectIO = "IO"
showEffect (EffectExcept _) = "Except"
showEffect (EffectState _) = "State"
showEffect (EffectReader _) = "Reader"
showEffect (EffectWriter _) = "Writer"
showEffect EffectAsync = "Async"
showEffect (EffectRow _) = "Row"

-- | Generate effect handler
generateEffectHandler :: EffectType -> T.Text
generateEffectHandler effect = case effect of
  EffectIO -> T.unlines
    [ "template<typename T>"
    , "T runEffect(IO<T> io) {"
    , "  return io.runIO();"
    , "}"
    ]
  EffectPure -> 
    "template<typename T>\nT runEffect(T value) { return value; }"
  _ -> "// Effect handler for " <> showEffect effect
