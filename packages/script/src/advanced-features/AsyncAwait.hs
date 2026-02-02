{-# LANGUAGE OverloadedStrings #-}
module AsyncAwait where

import qualified Data.Text as T
import GHC.Core

-- | Async/await support using C++20 coroutines
generateAsyncSupport :: T.Text
generateAsyncSupport = T.unlines
  [ "#include <coroutine>"
  , "#include <future>"
  , "#include <optional>"
  , ""
  , "namespace async_support {"
  , ""
  , "// Promise type for coroutines"
  , "template<typename T>"
  , "struct Promise {"
  , "  T value_;"
  , "  std::exception_ptr exception_;"
  , ""
  , "  auto get_return_object() {"
  , "    return std::coroutine_handle<Promise>::from_promise(*this);"
  , "  }"
  , ""
  , "  auto initial_suspend() { return std::suspend_never{}; }"
  , "  auto final_suspend() noexcept { return std::suspend_always{}; }"
  , ""
  , "  void unhandled_exception() {"
  , "    exception_ = std::current_exception();"
  , "  }"
  , ""
  , "  void return_value(T value) {"
  , "    value_ = std::move(value);"
  , "  }"
  , "};"
  , ""
  , "// Awaitable type"
  , "template<typename T>"
  , "struct Awaitable {"
  , "  std::coroutine_handle<> handle_;"
  , "  std::optional<T> value_;"
  , ""
  , "  bool await_ready() const noexcept { return value_.has_value(); }"
  , ""
  , "  void await_suspend(std::coroutine_handle<> h) {"
  , "    handle_ = h;"
  , "  }"
  , ""
  , "  T await_resume() {"
  , "    return std::move(*value_);"
  , "  }"
  , "};"
  , ""
  , "// Async task"
  , "template<typename T>"
  , "struct Task {"
  , "  using promise_type = Promise<T>;"
  , "  std::coroutine_handle<promise_type> handle_;"
  , ""
  , "  Task(std::coroutine_handle<promise_type> h) : handle_(h) {}"
  , ""
  , "  ~Task() {"
  , "    if (handle_) handle_.destroy();"
  , "  }"
  , ""
  , "  Task(const Task&) = delete;"
  , "  Task& operator=(const Task&) = delete;"
  , ""
  , "  Task(Task&& other) noexcept : handle_(other.handle_) {"
  , "    other.handle_ = {};"
  , "  }"
  , ""
  , "  Task& operator=(Task&& other) noexcept {"
  , "    if (this != &other) {"
  , "      if (handle_) handle_.destroy();"
  , "      handle_ = other.handle_;"
  , "      other.handle_ = {};"
  , "    }"
  , "    return *this;"
  , "  }"
  , ""
  , "  T get() {"
  , "    handle_.resume();"
  , "    return handle_.promise().value_;"
  , "  }"
  , "};"
  , ""
  , "// Async function generator"
  , "template<typename T>"
  , "Task<T> async(std::function<T()> computation) {"
  , "  co_return computation();"
  , "}"
  , ""
  , "// Await helper"
  , "template<typename T>"
  , "T await(Task<T> task) {"
  , "  return task.get();"
  , "}"
  , ""
  , "} // namespace async_support"
  ]

-- | Convert async expression to C++20 coroutine
asyncExprToCpp23 :: CoreExpr -> T.Text
asyncExprToCpp23 expr = 
  "co_return " <> coreExprToCpp23 expr <> ";"

-- | Convert await expression to C++20 coroutine
awaitExprToCpp23 :: CoreExpr -> T.Text
awaitExprToCpp23 expr = 
  "co_await " <> coreExprToCpp23 expr

-- | Helper to convert Core expression (simplified)
coreExprToCpp23 :: CoreExpr -> T.Text
coreExprToCpp23 expr = case expr of
  CoreVar v -> T.pack $ show $ varName v
  CoreLit lit -> literalToCpp lit
  CoreApp f x -> coreExprToCpp23 f <> "(" <> coreExprToCpp23 x <> ")"
  CoreLam v body -> "[](" <> T.pack (show $ varName v) <> ") { return " <> coreExprToCpp23 body <> "; }"
  CoreLet binds body -> 
    T.unlines (map (\(v, e) -> "auto " <> T.pack (show $ varName v) <> " = " <> coreExprToCpp23 e <> ";") binds) <>
    "return " <> coreExprToCpp23 body <> ";"
  CoreCase scrut var ty alts ->
    "std::visit([](auto&& v) -> auto {" <>
    T.unlines (map (\(CoreAlt con vars expr') -> 
      "  if constexpr (std::is_same_v<decltype(v), " <> conToCpp con <> ">) {" <>
      "    return " <> coreExprToCpp23 expr' <> ";" <>
      "  }") alts) <>
    "}, " <> coreExprToCpp23 scrut <> ")"
  CoreCast e _ -> coreExprToCpp23 e
  CoreTick _ e -> coreExprToCpp23 e
  CoreType _ -> "/* type */"
  CoreCoercion _ -> "/* coercion */"

literalToCpp :: Literal -> T.Text
literalToCpp (MachInt i) = T.pack $ show i
literalToCpp (MachInt64 i) = T.pack $ show i <> "LL"
literalToCpp (MachWord w) = T.pack $ show w <> "U"
literalToCpp (MachWord64 w) = T.pack $ show w <> "ULL"
literalToCpp (MachFloat f) = T.pack $ show f <> "f"
literalToCpp (MachDouble d) = T.pack $ show d
literalToCpp (MachChar c) = "\'" <> T.singleton c <> "\'"
literalToCpp (MachStr s) = "\"" <> T.pack s <> "\""
literalToCpp (MachNullAddr) = "nullptr"
literalToCpp (MachLabel _ _) = "/* label */"
literalToCpp (LitInteger i _) = T.pack $ show i

conToCpp :: AltCon -> T.Text
conToCpp (DataAlt dc) = T.pack $ show $ dataConName dc
conToCpp (LitAlt lit) = literalToCpp lit
conToCpp DEFAULT = "default"
