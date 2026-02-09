export const pow = function (base) {
  return function (exp) {
    return Math.pow(base, exp);
  };
};

export const floor = function (n) {
  return Math.floor(n);
};
