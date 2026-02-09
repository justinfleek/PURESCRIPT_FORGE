export const getViewportWidth = function() {
  return function() {
    return window.innerWidth || document.documentElement.clientWidth || 0;
  };
};

export const getViewportHeight = function() {
  return function() {
    return window.innerHeight || document.documentElement.clientHeight || 0;
  };
};
