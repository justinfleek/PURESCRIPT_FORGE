import { expect, afterEach, vi } from 'vitest';
import { cleanup } from '@testing-library/solid';
import '@testing-library/jest-dom/vitest';
import { register } from '@happy-dom/global-registrator';

// Register happy-dom for SolidJS component testing
register();

// Cleanup after each test
afterEach(() => {
  cleanup();
});

// Mock performance API for consistent benchmarks
global.performance = {
  ...performance,
  now: () => Date.now(),
  mark: vi.fn(),
  measure: vi.fn(),
  getEntriesByType: vi.fn(() => []),
  getEntriesByName: vi.fn(() => []),
  clearMarks: vi.fn(),
  clearMeasures: vi.fn(),
} as any;

// Mock ResizeObserver
global.ResizeObserver = class ResizeObserver {
  observe() {}
  unobserve() {}
  disconnect() {}
} as any;

// Mock IntersectionObserver
global.IntersectionObserver = class IntersectionObserver {
  constructor() {}
  observe() {}
  unobserve() {}
  disconnect() {}
} as any;

// Mock matchMedia
Object.defineProperty(window, 'matchMedia', {
  writable: true,
  value: vi.fn().mockImplementation(query => ({
    matches: false,
    media: query,
    onchange: null,
    addListener: vi.fn(),
    removeListener: vi.fn(),
    addEventListener: vi.fn(),
    removeEventListener: vi.fn(),
    dispatchEvent: vi.fn(),
  })),
});
