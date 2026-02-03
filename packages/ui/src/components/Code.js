// Code.js - FFI for Code component
// Wraps @pierre/diffs File renderer with shadow DOM access
// All functions are Effect Unit or Effect with concrete return types

import { File } from "@pierre/diffs";
import { getWorkerPool } from "../pierre/worker.js";

// Module state
let fileInstance = null;
let container = null;
let colorSchemeObserver = null;
let renderObserver = null;
let mouseUpHandler = null;

// Style variables from pierre
export const styleVariables = `
  --diffs-font-family: ui-monospace, SFMono-Regular, SF Mono, Menlo, Consolas, Liberation Mono, monospace;
  --diffs-font-size: 13px;
  --diffs-line-height: 1.5;
`;

// Create default options for File renderer
const createDefaultOptions = () => ({
  enableSplitDiff: false,
  enableLineNumbers: true,
  enableLineSelection: false,
  theme: "auto"
});

// Get shadow root from container
const getRoot = () => {
  if (!container) return null;
  const host = container.querySelector("diffs-container");
  if (!(host instanceof HTMLElement)) return null;
  return host.shadowRoot ?? null;
};

// Apply color scheme to container
const applyScheme = () => {
  const host = container?.querySelector("diffs-container");
  if (!(host instanceof HTMLElement)) return;

  const scheme = document.documentElement.dataset.colorScheme;
  if (scheme === "dark" || scheme === "light") {
    host.dataset.colorScheme = scheme;
    return;
  }
  host.removeAttribute("data-color-scheme");
};

// Render file using pierre/diffs File renderer
export const renderFileFFI = (containerEl) => (input) => () => {
  container = containerEl;
  
  // Cleanup previous instance
  if (fileInstance) {
    fileInstance.cleanUp();
    fileInstance = null;
  }
  
  // Clear container
  container.innerHTML = "";
  
  // Create new File instance
  const options = {
    ...createDefaultOptions(),
    enableLineNumbers: !input.disableLineNumbers,
    overflow: input.overflow
  };
  
  fileInstance = new File(options, getWorkerPool("unified"));
  
  // Render file
  fileInstance.render({
    file: {
      name: input.file.name ?? undefined,
      contents: input.file.contents,
      cacheKey: input.file.cacheKey ?? undefined
    },
    lineAnnotations: input.annotations.map(a => ({
      lineNumber: a.lineNumber,
      side: a.side ? sideToString(a.side) : undefined
    })),
    containerWrapper: container
  });
  
  // Apply color scheme
  applyScheme();
};

// Side conversion
const sideToString = (side) => {
  if (side && side.value0 === "Additions") return "additions";
  if (side && side.value0 === "Deletions") return "deletions";
  // Handle direct objects
  if (side === "Additions" || side?.tag === "Additions") return "additions";
  if (side === "Deletions" || side?.tag === "Deletions") return "deletions";
  return "additions";
};

// Cleanup file renderer
export const cleanupFile = () => {
  if (fileInstance) {
    fileInstance.cleanUp();
    fileInstance = null;
  }
  container = null;
};

// Apply selection to rendered lines
export const applySelection = (maybeRange) => (lineCount) => () => {
  if (!fileInstance) return;
  
  // Handle Maybe - null or object with value
  const range = maybeRange?.value0 ?? maybeRange?.value ?? maybeRange;
  if (!range || range.tag === "Nothing") {
    fileInstance.setSelectedLines(null);
    return;
  }
  
  const start = Math.min(range.start, range.end);
  const end = Math.max(range.start, range.end);
  
  if (start < 1 || end > lineCount) {
    fileInstance.setSelectedLines(null);
    return;
  }
  
  fileInstance.setSelectedLines({
    start: range.start,
    end: range.end,
    side: range.side ? sideToString(range.side) : undefined,
    endSide: range.endSide ? sideToString(range.endSide) : undefined
  });
};

// Apply commented lines styling
export const applyCommentedLines = (ranges) => () => {
  const root = getRoot();
  if (!root) return;
  
  // Clear existing selections
  const existing = Array.from(root.querySelectorAll("[data-comment-selected]"));
  for (const node of existing) {
    if (node instanceof HTMLElement) {
      node.removeAttribute("data-comment-selected");
    }
  }
  
  // Apply new selections
  for (const range of ranges) {
    const start = Math.max(1, Math.min(range.start, range.end));
    const end = Math.max(range.start, range.end);
    
    for (let line = start; line <= end; line++) {
      const nodes = Array.from(root.querySelectorAll(`[data-line="${line}"]`));
      for (const node of nodes) {
        if (node instanceof HTMLElement) {
          node.setAttribute("data-comment-selected", "");
        }
      }
    }
  }
};

// Setup color scheme monitoring
export const setupColorSchemeMonitor = () => {
  if (typeof MutationObserver === "undefined") return;
  
  cleanupColorSchemeMonitor();
  
  const root = document.documentElement;
  colorSchemeObserver = new MutationObserver(() => applyScheme());
  colorSchemeObserver.observe(root, { 
    attributes: true, 
    attributeFilter: ["data-color-scheme"] 
  });
};

// Cleanup color scheme monitor
export const cleanupColorSchemeMonitor = () => {
  if (colorSchemeObserver) {
    colorSchemeObserver.disconnect();
    colorSchemeObserver = null;
  }
};

// Setup global mouseup handler
export const setupGlobalMouseUp = () => {
  // This would need to integrate with Halogen's subscription system
  // For now, a placeholder
};

// Schedule render complete callback
export const scheduleRenderComplete = (callback) => () => {
  const root = getRoot();
  
  const isReady = (r) => r && r.querySelector("[data-line]") != null;
  
  const notify = () => {
    if (renderObserver) {
      renderObserver.disconnect();
      renderObserver = null;
    }
    requestAnimationFrame(() => callback());
  };
  
  if (root && isReady(root)) {
    notify();
    return;
  }
  
  if (typeof MutationObserver === "undefined") {
    requestAnimationFrame(() => callback());
    return;
  }
  
  const observeRoot = (r) => {
    if (isReady(r)) {
      notify();
      return;
    }
    
    if (renderObserver) {
      renderObserver.disconnect();
    }
    
    renderObserver = new MutationObserver(() => {
      if (isReady(r)) notify();
    });
    
    renderObserver.observe(r, { childList: true, subtree: true });
  };
  
  if (root) {
    observeRoot(root);
    return;
  }
  
  // Observe container for shadow root creation
  if (!container) {
    requestAnimationFrame(() => callback());
    return;
  }
  
  renderObserver = new MutationObserver(() => {
    const r = getRoot();
    if (r) observeRoot(r);
  });
  
  renderObserver.observe(container, { childList: true, subtree: true });
};

// Find element helper
const findElement = (node) => {
  if (!node) return undefined;
  if (node instanceof HTMLElement) return node;
  return node.parentElement ?? undefined;
};

// Find line number from node
const findLineNumber = (node) => {
  const element = findElement(node);
  if (!element) return undefined;
  
  const line = element.closest("[data-line]");
  if (!(line instanceof HTMLElement)) return undefined;
  
  const value = parseInt(line.dataset.line ?? "", 10);
  if (Number.isNaN(value)) return undefined;
  
  return value;
};

// Get line info from mouse event
export const lineFromMouseEvent = (event) => () => {
  const path = event.composedPath();
  
  let numberColumn = false;
  let line = undefined;
  
  for (const item of path) {
    if (!(item instanceof HTMLElement)) continue;
    
    numberColumn = numberColumn || item.dataset.columnNumber != null;
    
    if (line === undefined && item.dataset.line) {
      const parsed = parseInt(item.dataset.line, 10);
      if (!Number.isNaN(parsed)) line = parsed;
    }
    
    if (numberColumn && line !== undefined) break;
  }
  
  return { 
    line: line !== undefined ? { value0: line } : null,
    numberColumn 
  };
};

// Update selection from DOM selection API
export const updateSelectionFromDOM = () => {
  const root = getRoot();
  if (!root) return;
  
  const selection = root.getSelection?.() ?? window.getSelection();
  if (!selection || selection.isCollapsed) return;
  
  // Get composed ranges for shadow DOM
  const domRange = selection.getComposedRanges?.({ shadowRoots: [root] })?.[0] 
    ?? (selection.rangeCount > 0 ? selection.getRangeAt(0) : undefined);
  
  const startNode = domRange?.startContainer ?? selection.anchorNode;
  const endNode = domRange?.endContainer ?? selection.focusNode;
  if (!startNode || !endNode) return;
  
  if (!root.contains(startNode) || !root.contains(endNode)) return;
  
  const start = findLineNumber(startNode);
  const end = findLineNumber(endNode);
  if (start === undefined || end === undefined) return;
  
  // Selection range would be updated here
  // This integrates with the Halogen state management
};
