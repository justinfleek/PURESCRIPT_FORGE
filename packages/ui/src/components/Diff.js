// Diff.js - FFI for Diff component
// Wraps @pierre/diffs FileDiff renderer with shadow DOM access
// All functions are Effect Unit or Effect with concrete return types

import { checksum } from "@forge-ai/util/encode";
import { FileDiff } from "@pierre/diffs";
import { getWorkerPool } from "../pierre/worker.js";

// Module state
let diffInstance = null;
let container = null;
let colorSchemeObserver = null;
let renderObserver = null;
let onRenderComplete = null;

// Style variables from pierre
export const styleVariables = `
  --diffs-font-family: ui-monospace, SFMono-Regular, SF Mono, Menlo, Consolas, Liberation Mono, monospace;
  --diffs-font-size: 13px;
  --diffs-line-height: 1.5;
`;

// Create default options for FileDiff renderer
const createDefaultOptions = (diffStyle) => ({
  enableSplitDiff: diffStyle === "split",
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

// Side conversion
const sideToString = (side) => {
  if (!side) return undefined;
  if (side.value0 === "Additions" || side === "Additions" || side?.tag === "Additions") return "additions";
  if (side.value0 === "Deletions" || side === "Deletions" || side?.tag === "Deletions") return "deletions";
  return "additions";
};

const parseSide = (str) => {
  if (str === "additions") return { tag: "Additions" };
  if (str === "deletions") return { tag: "Deletions" };
  return null;
};

// Render diff using pierre/diffs FileDiff renderer
export const renderDiffFFI = (containerEl) => (input) => () => {
  container = containerEl;
  
  // Cleanup previous instance
  if (diffInstance) {
    diffInstance.cleanUp();
    diffInstance = null;
  }
  
  // Clear container
  container.innerHTML = "";
  
  // Create new FileDiff instance
  const diffStyle = input.diffStyle?.tag === "Split" ? "split" : "unified";
  const options = createDefaultOptions(diffStyle);
  
  diffInstance = new FileDiff(options, getWorkerPool(diffStyle));
  
  // Prepare file contents
  const beforeContents = input.before?.contents ?? "";
  const afterContents = input.after?.contents ?? "";
  
  // Render diff
  diffInstance.render({
    oldFile: {
      name: input.before?.name ?? undefined,
      contents: beforeContents,
      cacheKey: checksum(beforeContents)
    },
    newFile: {
      name: input.after?.name ?? undefined,
      contents: afterContents,
      cacheKey: checksum(afterContents)
    },
    lineAnnotations: input.annotations.map(a => ({
      lineNumber: a.lineNumber,
      side: sideToString(a.side)
    })),
    containerWrapper: container
  });
  
  // Apply color scheme
  applyScheme();
};

// Cleanup diff renderer
export const cleanupDiff = () => {
  if (diffInstance) {
    diffInstance.cleanUp();
    diffInstance = null;
  }
  container = null;
};

// Get line index from element
const lineIndex = (split, element) => {
  const raw = element.dataset.lineIndex;
  if (!raw) return undefined;
  const values = raw
    .split(",")
    .map(v => parseInt(v, 10))
    .filter(v => !Number.isNaN(v));
  if (values.length === 0) return undefined;
  if (!split) return values[0];
  if (values.length === 2) return values[1];
  return values[0];
};

// Get row index for line and side
const rowIndex = (root, split, line, side) => {
  const nodes = Array.from(root.querySelectorAll(`[data-line="${line}"], [data-alt-line="${line}"]`))
    .filter(node => node instanceof HTMLElement);
  if (nodes.length === 0) return undefined;

  const targetSide = side ?? "additions";

  for (const node of nodes) {
    if (findSide(node) === targetSide) return lineIndex(split, node);
    if (parseInt(node.dataset.altLine ?? "", 10) === line) return lineIndex(split, node);
  }
  return undefined;
};

// Find side from element
const findSide = (element) => {
  const line = element.closest("[data-line], [data-alt-line]");
  if (line instanceof HTMLElement) {
    const type = line.dataset.lineType;
    if (type === "change-deletion") return "deletions";
    if (type === "change-addition" || type === "change-additions") return "additions";
  }

  const code = element.closest("[data-code]");
  if (!(code instanceof HTMLElement)) return "additions";
  return code.hasAttribute("data-deletions") ? "deletions" : "additions";
};

// Fix selection to ensure proper ordering
const fixSelection = (range, diffStyle) => {
  if (!range) return range;
  const root = getRoot();
  if (!root) return undefined;

  const diffs = root.querySelector("[data-diffs]");
  if (!(diffs instanceof HTMLElement)) return undefined;

  const split = diffs.dataset.type === "split";
  const side = sideToString(range.side);
  const endSide = sideToString(range.endSide) ?? side;

  const start = rowIndex(root, split, range.start, side);
  const end = rowIndex(root, split, range.end, endSide);

  if (start === undefined || end === undefined) {
    if (root.querySelector("[data-line], [data-alt-line]") == null) return undefined;
    return null;
  }

  if (start <= end) return range;

  // Swap
  return {
    start: range.end,
    end: range.start,
    side: range.endSide,
    endSide: range.side
  };
};

// Apply selection to rendered diff lines
export const applyDiffSelection = (maybeRange) => (diffStyle) => () => {
  if (!diffInstance) return;
  
  const range = maybeRange?.value0 ?? maybeRange?.value ?? maybeRange;
  if (!range || range.tag === "Nothing") {
    diffInstance.setSelectedLines(null);
    return;
  }
  
  const fixed = fixSelection(range, diffStyle);
  if (fixed === undefined) {
    // DOM not ready, selection will be applied on render complete
    return;
  }
  if (fixed === null) {
    diffInstance.setSelectedLines(null);
    return;
  }
  
  diffInstance.setSelectedLines({
    start: fixed.start,
    end: fixed.end,
    side: sideToString(fixed.side),
    endSide: sideToString(fixed.endSide)
  });
};

// Apply commented lines styling to diff
export const applyDiffCommentedLines = (ranges) => (diffStyle) => () => {
  const root = getRoot();
  if (!root) return;
  
  // Clear existing selections
  const existing = Array.from(root.querySelectorAll("[data-comment-selected]"));
  for (const node of existing) {
    if (node instanceof HTMLElement) {
      node.removeAttribute("data-comment-selected");
    }
  }
  
  const diffs = root.querySelector("[data-diffs]");
  if (!(diffs instanceof HTMLElement)) return;
  
  const split = diffs.dataset.type === "split";
  
  const code = Array.from(diffs.querySelectorAll("[data-code]"))
    .filter(node => node instanceof HTMLElement);
  if (code.length === 0) return;
  
  for (const range of ranges) {
    const side = sideToString(range.side);
    const endSide = sideToString(range.endSide) ?? side;
    
    const start = rowIndex(root, split, range.start, side);
    if (start === undefined) continue;
    
    const same = range.end === range.start && (range.endSide == null || sideToString(range.endSide) === side);
    const end = same ? start : rowIndex(root, split, range.end, endSide);
    if (end === undefined) continue;
    
    const first = Math.min(start, end);
    const last = Math.max(start, end);
    
    for (const block of code) {
      for (const element of Array.from(block.children)) {
        if (!(element instanceof HTMLElement)) continue;
        const idx = lineIndex(split, element);
        if (idx === undefined) continue;
        if (idx > last) break;
        if (idx < first) continue;
        element.setAttribute("data-comment-selected", "");
        const next = element.nextSibling;
        if (next instanceof HTMLElement && next.hasAttribute("data-line-annotation")) {
          next.setAttribute("data-comment-selected", "");
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

// Schedule diff render complete
export const scheduleDiffRenderComplete = () => {
  const root = getRoot();
  let settle = 0;
  
  const isReady = (r) => r && r.querySelector("[data-line]") != null;
  
  const notify = () => {
    if (renderObserver) {
      renderObserver.disconnect();
      renderObserver = null;
    }
    // Render complete notification handled by Halogen
  };
  
  const schedule = () => {
    settle++;
    const current = settle;
    
    requestAnimationFrame(() => {
      if (current !== settle) return;
      requestAnimationFrame(() => {
        if (current !== settle) return;
        notify();
      });
    });
  };
  
  if (root && isReady(root)) {
    schedule();
    return;
  }
  
  if (typeof MutationObserver === "undefined") {
    requestAnimationFrame(notify);
    return;
  }
  
  const observeRoot = (r) => {
    if (renderObserver) {
      renderObserver.disconnect();
    }
    
    renderObserver = new MutationObserver(() => {
      if (isReady(r)) schedule();
    });
    
    renderObserver.observe(r, { childList: true, subtree: true });
    
    if (isReady(r)) schedule();
  };
  
  if (root) {
    observeRoot(root);
    return;
  }
  
  if (!container) {
    requestAnimationFrame(notify);
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
  
  const line = element.closest("[data-line], [data-alt-line]");
  if (!(line instanceof HTMLElement)) return undefined;
  
  const primary = parseInt(line.dataset.line ?? "", 10);
  if (!Number.isNaN(primary)) return primary;
  
  const alt = parseInt(line.dataset.altLine ?? "", 10);
  if (!Number.isNaN(alt)) return alt;
  
  return undefined;
};

// Get line info from mouse event (with side awareness)
export const diffLineFromMouseEvent = (event) => () => {
  const path = event.composedPath();
  
  let numberColumn = false;
  let line = undefined;
  let side = undefined;
  
  for (const item of path) {
    if (!(item instanceof HTMLElement)) continue;
    
    numberColumn = numberColumn || item.dataset.columnNumber != null;
    
    if (side === undefined) {
      const type = item.dataset.lineType;
      if (type === "change-deletion") side = { tag: "Deletions" };
      else if (type === "change-addition" || type === "change-additions") side = { tag: "Additions" };
    }
    
    if (side === undefined && item.dataset.code != null) {
      side = item.hasAttribute("data-deletions") ? { tag: "Deletions" } : { tag: "Additions" };
    }
    
    if (line === undefined) {
      const primary = item.dataset.line ? parseInt(item.dataset.line, 10) : Number.NaN;
      if (!Number.isNaN(primary)) {
        line = primary;
      } else {
        const alt = item.dataset.altLine ? parseInt(item.dataset.altLine, 10) : Number.NaN;
        if (!Number.isNaN(alt)) line = alt;
      }
    }
    
    if (numberColumn && line !== undefined && side !== undefined) break;
  }
  
  return { 
    line: line !== undefined ? { value0: line } : null,
    numberColumn,
    side: side ?? null
  };
};

// Update selection from DOM selection API
export const updateDiffSelectionFromDOM = () => {
  const root = getRoot();
  if (!root) return;
  
  const selection = root.getSelection?.() ?? window.getSelection();
  if (!selection || selection.isCollapsed) return;
  
  const domRange = selection.getComposedRanges?.({ shadowRoots: [root] })?.[0] 
    ?? (selection.rangeCount > 0 ? selection.getRangeAt(0) : undefined);
  
  const startNode = domRange?.startContainer ?? selection.anchorNode;
  const endNode = domRange?.endContainer ?? selection.focusNode;
  if (!startNode || !endNode) return;
  
  if (!root.contains(startNode) || !root.contains(endNode)) return;
  
  const start = findLineNumber(startNode);
  const end = findLineNumber(endNode);
  if (start === undefined || end === undefined) return;
  
  const startElement = findElement(startNode);
  const endElement = findElement(endNode);
  
  const startSide = startElement ? parseSide(findSide(startElement)) : null;
  const endSide = endElement ? parseSide(findSide(endElement)) : null;
  
  // Selection range would be updated here via Halogen state
};
