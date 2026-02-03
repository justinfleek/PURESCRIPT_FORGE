/**
 * Performance testing utilities
 */

export interface PerformanceMetrics {
  renderTime: number;
  updateTime: number;
  memoryUsage?: number;
  frameCount?: number;
}

/**
 * Measure component render performance
 */
export async function measureRender<T>(
  renderFn: () => T,
  iterations: number = 100
): Promise<PerformanceMetrics> {
  const times: number[] = [];
  let result: T;

  // Warmup
  for (let i = 0; i < 10; i++) {
    renderFn();
  }

  // Measure
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    result = renderFn();
    const end = performance.now();
    times.push(end - start);
  }

  const renderTime = times.reduce((a, b) => a + b, 0) / times.length;

  return {
    renderTime,
    updateTime: 0, // Will be measured separately
  };
}

/**
 * Measure component update performance
 */
export async function measureUpdate<T>(
  updateFn: () => T,
  iterations: number = 100
): Promise<number> {
  const times: number[] = [];

  // Warmup
  for (let i = 0; i < 10; i++) {
    updateFn();
  }

  // Measure
  for (let i = 0; i < iterations; i++) {
    const start = performance.now();
    updateFn();
    const end = performance.now();
    times.push(end - start);
  }

  return times.reduce((a, b) => a + b, 0) / times.length;
}

/**
 * Measure memory usage
 */
export function measureMemory(): number | undefined {
  if ('memory' in performance) {
    return (performance as any).memory.usedJSHeapSize;
  }
  return undefined;
}

/**
 * Performance benchmark with thresholds
 */
export interface BenchmarkThresholds {
  maxRenderTime?: number;
  maxUpdateTime?: number;
  maxMemoryUsage?: number;
}

export function assertPerformance(
  metrics: PerformanceMetrics,
  thresholds: BenchmarkThresholds
): void {
  if (thresholds.maxRenderTime && metrics.renderTime > thresholds.maxRenderTime) {
    throw new Error(
      `Render time ${metrics.renderTime}ms exceeds threshold ${thresholds.maxRenderTime}ms`
    );
  }

  if (thresholds.maxUpdateTime && metrics.updateTime > thresholds.maxUpdateTime) {
    throw new Error(
      `Update time ${metrics.updateTime}ms exceeds threshold ${thresholds.maxUpdateTime}ms`
    );
  }

  if (
    thresholds.maxMemoryUsage &&
    metrics.memoryUsage &&
    metrics.memoryUsage > thresholds.maxMemoryUsage
  ) {
    throw new Error(
      `Memory usage ${metrics.memoryUsage} bytes exceeds threshold ${thresholds.maxMemoryUsage} bytes`
    );
  }
}
