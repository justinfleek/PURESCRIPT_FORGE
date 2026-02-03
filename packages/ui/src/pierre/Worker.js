// FFI for Forge.UI.Pierre.Worker
// Wraps @pierre/diffs worker pool management

import { WorkerPoolManager } from "@pierre/diffs/worker";
import ShikiWorkerUrl from "@pierre/diffs/worker/worker.js?worker&url";

// Memoized pools
let unified = undefined;
let split = undefined;

// Create a new worker instance
function createWorker() {
  return new Worker(ShikiWorkerUrl, { type: "module" });
}

// Create a worker pool with the given line diff type
function createPool(lineDiffType) {
  const pool = new WorkerPoolManager(
    {
      workerFactory: createWorker,
      // Pool size of 2 is optimal for OpenCode
      // More workers = more parallelism but also more memory
      // Safari has slower worker boot times, so keep this low
      poolSize: 2,
    },
    {
      theme: "OpenCode",
      lineDiffType,
    }
  );

  pool.initialize();
  return pool;
}

// FFI: Create a worker (returns the factory result)
export function workerFactory() {
  return function() {
    return createWorker();
  };
}

// FFI: Get or create a worker pool for the given style
// Returns Nothing on server-side (no window)
export function getWorkerPool(style) {
  return function() {
    // Server-side check
    if (typeof window === "undefined") {
      return null; // PureScript Maybe Nothing
    }

    if (style === "split" || style.value0 === "SplitPool") {
      if (!split) {
        split = createPool("word-alt");
      }
      return split;
    }

    // Default to unified
    if (!unified) {
      unified = createPool("none");
    }
    return unified;
  };
}

// FFI: Get both worker pools
export function getWorkerPools() {
  return function() {
    return {
      unified: getWorkerPool("unified")(),
      split: getWorkerPool("split")(),
    };
  };
}
