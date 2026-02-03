// DiffSsr.js - FFI for SSR Diff component
// Hydrates server-rendered diff with @pierre/diffs FileDiff
// All functions are Effect Unit or Effect with concrete return types

import { DIFFS_TAG_NAME, FileDiff } from "@pierre/diffs";
import { getWorkerPool } from "../pierre/worker.js";

// Module state
let diffInstance = null;
let container = null;
let diffsContainer = null;
let colorSchemeObserver = null;

// Style variables from pierre
export const styleVariables = `
  --diffs-font-family: ui-monospace, SFMono-Regular, SF Mono, Menlo, Consolas, Liberation Mono, monospace;
  --diffs-font-size: 13px;
  --diffs-line-height: 1.5;
`;

// DIFFS_TAG_NAME constant
export const diffsTagName = DIFFS_TAG_NAME ?? "diffs-container";

// Check if running on server
export const isServer = typeof window === "undefined";

// Get shadow root from diffs container
const getRoot = () => {
  if (!diffsContainer) return null;
  return diffsContainer.shadowRoot ?? null;
};

// Apply color scheme
export const applyScheme = () => {
  if (!diffsContainer) return;
  
  const scheme = document.documentElement.dataset.colorScheme;
  if (scheme === "dark" || scheme === "light") {
    diffsContainer.dataset.colorScheme = scheme;
    return;
  }
  diffsContainer.removeAttribute("data-color-scheme");
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

// Side conversion helpers
const sideToString = (side) => {
  if (!side) return undefined;
  if (side.value0 === "Additions" || side === "Additions" || side?.tag === "Additions") return "additions";
  if (side.value0 === "Deletions" || side === "Deletions" || side?.tag === "Deletions") return "deletions";
  return "additions";
};

// Create default options for FileDiff renderer
const createDefaultOptions = (diffStyle) => ({
  enableSplitDiff: diffStyle === "split",
  enableLineNumbers: true,
  enableLineSelection: false,
  theme: "auto"
});

// Hydrate SSR diff content
export const hydrateDiffFFI = (containerEl) => (diffsContainerEl) => (input) => () => {
  container = containerEl;
  diffsContainer = diffsContainerEl;
  
  // Cleanup previous instance
  if (diffInstance) {
    diffInstance.cleanUp();
    diffInstance = null;
  }
  
  // Create new FileDiff instance with preloaded options
  const diffStyle = input.diffStyle?.tag === "Split" ? "split" : "unified";
  const options = {
    ...createDefaultOptions(diffStyle),
    ...input.preloadedDiff
  };
  
  diffInstance = new FileDiff(options, getWorkerPool(diffStyle));
  
  // Set fileContainer for SSR hydration
  // @ts-expect-error - fileContainer is private but needed for SSR hydration
  diffInstance.fileContainer = diffsContainer;
  
  // Hydrate
  diffInstance.hydrate({
    oldFile: input.before ?? undefined,
    newFile: input.after ?? undefined,
    lineAnnotations: input.annotations.map(a => ({
      lineNumber: a.lineNumber,
      side: sideToString(a.side)
    })),
    fileContainer: diffsContainer,
    containerWrapper: container
  });
};

// Cleanup SSR diff
export const cleanupDiffSsr = () => {
  if (diffInstance) {
    diffInstance.cleanUp();
    diffInstance = null;
  }
  container = null;
  diffsContainer = null;
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

// Fix selection to ensure proper ordering
const fixSelection = (range) => {
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

  return {
    start: range.end,
    end: range.start,
    side: range.endSide,
    endSide: range.side
  };
};

// Set selected lines on SSR diff (with retry)
export const setSelectedLinesSsr = (maybeRange) => () => {
  if (!diffInstance) return;
  
  const range = maybeRange?.value0 ?? maybeRange?.value ?? maybeRange;
  if (!range || range.tag === "Nothing") {
    diffInstance.setSelectedLines(null);
    return;
  }
  
  const setWithRetry = (attempt) => {
    const fixed = fixSelection(range);
    if (fixed === undefined) {
      if (attempt >= 120) return;
      requestAnimationFrame(() => setWithRetry(attempt + 1));
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
  
  setWithRetry(0);
};

// Set annotations on SSR diff
export const setAnnotationsSsr = (annotations) => () => {
  if (!diffInstance) return;
  
  diffInstance.setLineAnnotations(
    annotations.map(a => ({
      lineNumber: a.lineNumber,
      side: sideToString(a.side)
    }))
  );
};

// Apply commented lines styling to SSR diff
export const applyCommentedLinesSsr = (ranges) => (diffStyle) => () => {
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
