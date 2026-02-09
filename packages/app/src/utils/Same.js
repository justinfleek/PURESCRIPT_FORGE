// FFI for Sidepanel.Utils.Same
export const unsafeRefEq = function (a) {
  return function (b) {
    return a === b;
  };
};
