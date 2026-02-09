// FFI for Sidepanel.Utils.Base64
export const base64DecodeImpl = function (value) {
  return function () {
    return atob(value);
  };
};
