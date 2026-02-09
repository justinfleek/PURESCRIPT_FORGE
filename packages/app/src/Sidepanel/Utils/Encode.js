export const base64Encode = function (str) {
  try {
    return btoa(unescape(encodeURIComponent(str)));
  } catch (e) {
    return btoa(str);
  }
};
