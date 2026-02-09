// FFI for Sidepanel.Utils.Dom

export const getCharacterOffsetInLineImpl = function (lineElement) {
  return function (targetNode) {
    return function (offset) {
      return function () {
        try {
          var range = document.createRange();
          range.selectNodeContents(lineElement);
          range.setEnd(targetNode, offset);
          return range.toString().length;
        } catch (e) {
          return 0;
        }
      };
    };
  };
};

export const getNodeOffsetInLineImpl = function (lineElement) {
  return function (charIndex) {
    return function () {
      try {
        var walker = document.createTreeWalker(
          lineElement,
          NodeFilter.SHOW_TEXT,
          null,
          false
        );
        var remaining = charIndex;
        var node;
        while ((node = walker.nextNode())) {
          var len = node.textContent ? node.textContent.length : 0;
          if (remaining <= len) {
            return { node: node, offset: remaining };
          }
          remaining -= len;
        }
        return null;
      } catch (e) {
        return null;
      }
    };
  };
};

export const getSelectionInContainerImpl = function (container) {
  return function () {
    try {
      var sel = window.getSelection();
      if (!sel || sel.rangeCount === 0) return null;

      var range = sel.getRangeAt(0);
      if (!container.contains(range.startContainer) || !container.contains(range.endContainer)) {
        return null;
      }

      var lines = container.querySelectorAll(".line");
      var startLine = -1;
      var endLine = -1;

      for (var i = 0; i < lines.length; i++) {
        if (lines[i].contains(range.startContainer)) startLine = i;
        if (lines[i].contains(range.endContainer)) endLine = i;
      }

      if (startLine === -1 || endLine === -1) return null;

      return {
        sl: startLine + 1,
        sch: 0,
        el: endLine + 1,
        ech: 0
      };
    } catch (e) {
      return null;
    }
  };
};
