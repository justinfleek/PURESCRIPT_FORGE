// | Prevent default event behavior
export const preventDefault = function(event) {
  return function() {
    if (event && event.preventDefault) {
      event.preventDefault();
    }
  };
};

// | Check if input element has focus
export const isInputFocused = function(event) {
  return function() {
    if (!event || !event.target) {
      return false;
    }
    var tagName = event.target.tagName;
    return tagName === "INPUT" || tagName === "TEXTAREA" || tagName === "SELECT";
  };
};
