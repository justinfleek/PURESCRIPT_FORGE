// FFI for Sidepanel.Utils.Prompt

// parseInt :: String -> Maybe Int
export const parseInt = function (str) {
  var result = globalThis.parseInt(str, 10);
  if (isNaN(result)) {
    return { constructor: { name: "Nothing" } };
  }
  return { constructor: { name: "Just" }, value0: result };
};
