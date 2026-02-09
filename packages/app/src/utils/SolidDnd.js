// FFI for Sidepanel.Utils.SolidDnd

export const getDraggableIdImpl = function(event) {
  try {
    if (event && event.draggable && typeof event.draggable.id === "string") {
      return { constructor: { name: "Just" }, value0: event.draggable.id };
    }
  } catch (e) {}
  return { constructor: { name: "Nothing" } };
};

export const addTransformer = function(namespace) {
  return function(id) {
    return function(transformer) {
      return function() {
        // No-op in non-solid-dnd environment
      };
    };
  };
};

export const removeTransformer = function(namespace) {
  return function(id) {
    return function(transformerId) {
      return function() {
        // No-op in non-solid-dnd environment
      };
    };
  };
};

export const useDragDropContext = function() {
  return { constructor: { name: "Nothing" } };
};

export const onDragStart = function(handler) {
  return function() {
    // No-op
  };
};

export const onDragEnd = function(handler) {
  return function() {
    // No-op
  };
};
